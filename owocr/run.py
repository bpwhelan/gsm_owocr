import os
import sys

from GameSentenceMiner.ocr.gsm_ocr_config import set_dpi_awareness, get_scene_ocr_config
from GameSentenceMiner.util.gsm_utils import do_text_replacements, OCR_REPLACEMENTS_FILE
from GameSentenceMiner.util.electron_config import get_ocr_language, get_ocr_ocr2, get_ocr_requires_open_window, \
    has_ocr_config_changed, reload_electron_config, get_ocr_scan_rate, get_ocr_two_pass_ocr, get_ocr_keep_newline, \
    get_ocr_ocr1, get_furigana_filter_sensitivity
import signal
import time
import threading
from pathlib import Path
import queue
import io
import re
import logging
import inspect
import os
import json
import collections
from dataclasses import asdict

import numpy as np
import pyperclipfix
import mss
import psutil
import asyncio
import websockets
import socket
import socketserver

from PIL import Image, UnidentifiedImageError
from loguru import logger
from pynput import keyboard
from desktop_notifier import DesktopNotifierSync, Urgency

from .ocr import *
from .config import config
from .screen_coordinate_picker import get_screen_selection, terminate_selector_if_running

try:
    import win32gui
    import win32ui
    import win32api
    import win32con
    import win32process
    import win32clipboard
    import pywintypes
    import ctypes
except ImportError:
    pass

try:
    import objc
    import platform
    from AppKit import NSData, NSImage, NSBitmapImageRep, NSDeviceRGBColorSpace, NSGraphicsContext, NSZeroPoint, NSZeroRect, NSCompositingOperationCopy
    from Quartz import CGWindowListCreateImageFromArray, kCGWindowImageBoundsIgnoreFraming, CGRectMake, CGRectNull, CGMainDisplayID, CGWindowListCopyWindowInfo, \
                       CGWindowListCreateDescriptionFromArray, kCGWindowListOptionOnScreenOnly, kCGWindowListExcludeDesktopElements, kCGWindowListOptionIncludingWindow, \
                       kCGWindowName, kCGNullWindowID, CGImageGetWidth, CGImageGetHeight, CGDataProviderCopyData, CGImageGetDataProvider, CGImageGetBytesPerRow, \
                       kCGWindowImageNominalResolution
    from ScreenCaptureKit import SCContentFilter, SCScreenshotManager, SCShareableContent, SCStreamConfiguration, SCCaptureResolutionNominal
except ImportError:
    pass

import signal
import threading
from pathlib import Path
import queue
import re
import logging
import inspect
import time

import pyperclipfix
import mss
import asyncio
import websockets
import socketserver
import cv2
import numpy as np

from collections import deque
from datetime import datetime, timedelta
from PIL import Image, ImageDraw
from loguru import logger
from desktop_notifier import DesktopNotifierSync
import psutil

from .ocr import *  # noqa: F403
from .config import Config
from .screen_coordinate_picker import get_screen_selection
from GameSentenceMiner.util.configuration import get_config, get_temporary_directory

from skimage.metrics import structural_similarity as ssim
from typing import Union

config = None
last_image = None
last_image_np = None


class ClipboardThread(threading.Thread):
    def __init__(self):
        super().__init__(daemon=True)
        self.delay_secs = config.get_general('delay_secs')
        self.last_update = time.time()

    def are_images_identical(self, img1, img2):
        if None in (img1, img2):
            return img1 == img2

        img1 = np.array(img1)
        img2 = np.array(img2)

        return (img1.shape == img2.shape) and (img1 == img2).all()

    def normalize_macos_clipboard(self, img):
        ns_data = NSData.dataWithBytes_length_(img, len(img))
        ns_image = NSImage.alloc().initWithData_(ns_data)

        new_image = NSBitmapImageRep.alloc().initWithBitmapDataPlanes_pixelsWide_pixelsHigh_bitsPerSample_samplesPerPixel_hasAlpha_isPlanar_colorSpaceName_bytesPerRow_bitsPerPixel_(
            None,  # Set to None to create a new bitmap
            int(ns_image.size().width),
            int(ns_image.size().height),
            8,  # Bits per sample
            4,  # Samples per pixel (R, G, B, A)
            True,  # Has alpha
            False,  # Is not planar
            NSDeviceRGBColorSpace,
            0,  # Automatically compute bytes per row
            32  # Bits per pixel (8 bits per sample * 4 samples per pixel)
        )

        context = NSGraphicsContext.graphicsContextWithBitmapImageRep_(
            new_image)
        NSGraphicsContext.setCurrentContext_(context)

        ns_image.drawAtPoint_fromRect_operation_fraction_(
            NSZeroPoint,
            NSZeroRect,
            NSCompositingOperationCopy,
            1.0
        )

        return bytes(new_image.TIFFRepresentation())

    def process_message(self, hwnd: int, msg: int, wparam: int, lparam: int):
        WM_CLIPBOARDUPDATE = 0x031D
        timestamp = time.time()
        if msg == WM_CLIPBOARDUPDATE and timestamp - self.last_update > 1 and not paused.is_set():
            self.last_update = timestamp
            while True:
                try:
                    win32clipboard.OpenClipboard()
                    break
                except pywintypes.error:
                    pass
                time.sleep(0.1)
            try:
                if win32clipboard.IsClipboardFormatAvailable(win32con.CF_BITMAP) and win32clipboard.IsClipboardFormatAvailable(win32clipboard.CF_DIB):
                    img = win32clipboard.GetClipboardData(win32clipboard.CF_DIB)
                    image_queue.put((img, False))
                win32clipboard.CloseClipboard()
            except pywintypes.error:
                pass
        return 0

    def create_window(self):
        className = 'ClipboardHook'
        wc = win32gui.WNDCLASS()
        wc.lpfnWndProc = self.process_message
        wc.lpszClassName = className
        wc.hInstance = win32api.GetModuleHandle(None)
        class_atom = win32gui.RegisterClass(wc)
        return win32gui.CreateWindow(class_atom, className, 0, 0, 0, 0, 0, 0, 0, wc.hInstance, None)

    def run(self):
        if sys.platform == 'win32':
            hwnd = self.create_window()
            self.thread_id = win32api.GetCurrentThreadId()
            ctypes.windll.user32.AddClipboardFormatListener(hwnd)
            win32gui.PumpMessages()
        else:
            is_macos = sys.platform == 'darwin'
            if is_macos:
                from AppKit import NSPasteboard, NSPasteboardTypeTIFF
                pasteboard = NSPasteboard.generalPasteboard()
                count = pasteboard.changeCount()
            else:
                from PIL import ImageGrab
            process_clipboard = False
            img = None

            while not terminated.is_set():
                if paused.is_set():
                    sleep_time = 0.5
                    process_clipboard = False
                else:
                    sleep_time = self.delay_secs
                    if is_macos:
                        with objc.autorelease_pool():
                            old_count = count
                            count = pasteboard.changeCount()
                            if process_clipboard and count != old_count:
                                wait_counter = 0
                                while len(pasteboard.types()) == 0 and wait_counter < 3:
                                    time.sleep(0.1)
                                    wait_counter += 1
                                if NSPasteboardTypeTIFF in pasteboard.types():
                                    img = self.normalize_macos_clipboard(pasteboard.dataForType_(NSPasteboardTypeTIFF))
                                    image_queue.put((img, False))
                    else:
                        old_img = img
                        try:
                            img = ImageGrab.grabclipboard()
                        except Exception:
                            pass
                        else:
                            if (process_clipboard and isinstance(img, Image.Image) and \
                                (not self.are_images_identical(img, old_img))):
                                image_queue.put((img, False))

                    process_clipboard = True

                if not terminated.is_set():
                    time.sleep(sleep_time)


class DirectoryWatcher(threading.Thread):
    def __init__(self, path):
        super().__init__(daemon=True)
        self.path = path
        self.delay_secs = config.get_general('delay_secs')
        self.last_update = time.time()
        self.allowed_extensions = (
            '.png', '.jpg', '.jpeg', '.bmp', '.gif', '.webp')

    def get_path_key(self, path):
        return path, path.lstat().st_mtime

    def run(self):
        old_paths = set()
        for path in self.path.iterdir():
            if path.suffix.lower() in self.allowed_extensions:
                old_paths.add(self.get_path_key(path))

        while not terminated.is_set():
            if paused.is_set():
                sleep_time = 0.5
            else:
                sleep_time = self.delay_secs
                for path in self.path.iterdir():
                    if path.suffix.lower() in self.allowed_extensions:
                        path_key = self.get_path_key(path)
                        if path_key not in old_paths:
                            old_paths.add(path_key)

                            if not paused.is_set():
                                image_queue.put((path, False))

            if not terminated.is_set():
                time.sleep(sleep_time)


class WebsocketServerThread(threading.Thread):
    def __init__(self, read):
        super().__init__(daemon=True)
        self._loop = None
        self.read = read
        self.clients = set()
        self._event = threading.Event()

    @property
    def loop(self):
        self._event.wait()
        return self._loop

    async def send_text_coroutine(self, text):
        for client in self.clients:
            await client.send(text)

    async def server_handler(self, websocket):
        self.clients.add(websocket)
        try:
            async for message in websocket:
                if self.read and not paused.is_set():
                    image_queue.put((message, False))
                    try:
                        await websocket.send('True')
                    except websockets.exceptions.ConnectionClosedOK:
                        pass
                else:
                    try:
                        await websocket.send('False')
                    except websockets.exceptions.ConnectionClosedOK:
                        pass
        except websockets.exceptions.ConnectionClosedError:
            pass
        finally:
            self.clients.remove(websocket)

    def send_text(self, text):
        return asyncio.run_coroutine_threadsafe(self.send_text_coroutine(text), self.loop)

    def stop_server(self):
        try:
            self.loop.call_soon_threadsafe(self._stop_event.set)
        except RuntimeError:
            pass

    def run(self):
        async def main():
            self._loop = asyncio.get_running_loop()
            self._stop_event = stop_event = asyncio.Event()
            self._event.set()
            websocket_port = config.get_general('websocket_port')
            self.server = start_server = websockets.serve(self.server_handler, get_config().advanced.localhost_bind_address, websocket_port, max_size=1000000000)
            try:
                async with start_server:
                    await stop_event.wait()
            except OSError:
                exit_with_error(f"Couldn't start websocket server. Make sure port {websocket_port} is not already in use")
        asyncio.run(main())


class UnixSocketRequestHandler(socketserver.BaseRequestHandler):
    def handle(self):
        conn = self.request
        conn.settimeout(3)
        data = conn.recv(4)
        img_size = int.from_bytes(data)
        img = bytearray()
        try:
            while len(img) < img_size:
                data = conn.recv(4096)
                if not data:
                    break
                img.extend(data)
        except TimeoutError:
            pass

        try:
            if not paused.is_set():
                image_queue.put((img, False))
                conn.sendall(b'True')
            else:
                conn.sendall(b'False')
        except:
            pass


class PassthroughSegmenter:
    def segment(self, text):
        return [text]

class TextFiltering:
    accurate_filtering = False

    # def __init__(self, lang='ja'):
    #     from pysbd import Segmenter, languages
    #     self.initial_lang = get_ocr_language() or lang
    #     if lang in languages.LANGUAGE_CODES:
    #         self.segmenter = Segmenter(language=lang, clean=True)
    #     else:
    #         self.segmenter = PassthroughSegmenter()
    #     self.kana_kanji_regex = re.compile(
    #         r'[\u3041-\u3096\u30A1-\u30FA\u4E00-\u9FFF]')
    #     self.chinese_common_regex = re.compile(r'[\u4E00-\u9FFF]')
    #     self.english_regex = re.compile(r'[a-zA-Z0-9.,!?;:"\'()\[\]{}]')
    #     self.chinese_common_regex = re.compile(r'[\u4E00-\u9FFF]')
    #     self.english_regex = re.compile(r'[a-zA-Z0-9.,!?;:"\'()\[\]{}]')
    #     self.korean_regex = re.compile(r'[\uAC00-\uD7AF]')
    #     self.arabic_regex = re.compile(
    #         r'[\u0600-\u06FF\u0750-\u077F\u08A0-\u08FF\uFB50-\uFDFF\uFE70-\uFEFF]')
    #     self.russian_regex = re.compile(
    #         r'[\u0400-\u04FF\u0500-\u052F\u2DE0-\u2DFF\uA640-\uA69F\u1C80-\u1C8F]')
    #     self.greek_regex = re.compile(r'[\u0370-\u03FF\u1F00-\u1FFF]')
    #     self.hebrew_regex = re.compile(r'[\u0590-\u05FF\uFB1D-\uFB4F]')
    #     self.thai_regex = re.compile(r'[\u0E00-\u0E7F]')
    #     self.latin_extended_regex = re.compile(
    #         r'[a-zA-Z\u00C0-\u00FF\u0100-\u017F\u0180-\u024F\u0250-\u02AF\u1D00-\u1D7F\u1D80-\u1DBF\u1E00-\u1EFF\u2C60-\u2C7F\uA720-\uA7FF\uAB30-\uAB6F]')
    #     self.last_few_results = {}
    #     try:
    #         from transformers import pipeline, AutoTokenizer
    #         import torch
    #         logging.getLogger('transformers').setLevel(logging.ERROR)

    #         model_ckpt = 'papluca/xlm-roberta-base-language-detection'
    #         tokenizer = AutoTokenizer.from_pretrained(
    #             model_ckpt,
    #             use_fast=False
    def __init__(self):
        self.language = get_ocr_language() or 'ja'
        self.json_output = config.get_general('output_format') == 'json'
        self.frame_stabilization = 0 if config.get_general('screen_capture_delay_secs') == -1 else config.get_general('screen_capture_frame_stabilization')
        self.line_recovery = not self.json_output and config.get_general('screen_capture_line_recovery')
        self.furigana_filter = config.get_general('furigana_filter')
        self.debug_filtering = config.get_general('uwu')
        self.last_frame_data = (None, None)
        self.last_last_frame_data = (None, None)
        self.stable_frame_data = None
        self.last_frame_text = []
        self.last_last_frame_text = []
        self.stable_frame_text = []
        self.processed_stable_frame = False
        self.frame_stabilization_timestamp = 0
        self.cj_regex = re.compile(r'[\u3041-\u3096\u30A1-\u30FA\u4E01-\u9FFF]')
        self.kanji_regex = re.compile(r'[\u4E00-\u9FFF]')
        self.regex = self._get_regex()
        self.manual_regex_filter = self._get_manual_regex_filter()
        self.kana_variants = {
            'ぁ': ['ぁ', 'あ'], 'あ': ['ぁ', 'あ'],
            'ぃ': ['ぃ', 'い'], 'い': ['ぃ', 'い'],
            'ぅ': ['ぅ', 'う'], 'う': ['ぅ', 'う'],
            'ぇ': ['ぇ', 'え'], 'え': ['ぇ', 'え'],
            'ぉ': ['ぉ', 'お'], 'お': ['ぉ', 'お'],
            'ァ': ['ァ', 'ア'], 'ア': ['ァ', 'ア'],
            'ィ': ['ィ', 'イ'], 'イ': ['ィ', 'イ'],
            'ゥ': ['ゥ', 'ウ'], 'ウ': ['ゥ', 'ウ'],
            'ェ': ['ェ', 'エ'], 'エ': ['ェ', 'エ'],
            'ォ': ['ォ', 'オ'], 'オ': ['ォ', 'オ'],
            'ゃ': ['ゃ', 'や'], 'や': ['ゃ', 'や'],
            'ゅ': ['ゅ', 'ゆ'], 'ゆ': ['ゅ', 'ゆ'],
            'ょ': ['ょ', 'よ'], 'よ': ['ょ', 'よ'],
            'ャ': ['ャ', 'ヤ'], 'ヤ': ['ャ', 'ヤ'],
            'ュ': ['ュ', 'ユ'], 'ユ': ['ュ', 'ユ'],
            'ョ': ['ョ', 'ヨ'], 'ヨ': ['ョ', 'ヨ'],
            'っ': ['っ', 'つ'], 'つ': ['っ', 'つ'],
            'ッ': ['ッ', 'ツ'], 'ツ': ['ッ', 'ツ'],
            'ゎ': ['ゎ', 'わ'], 'わ': ['ゎ', 'わ'],
            'ヮ': ['ヮ', 'ワ'], 'ワ': ['ヮ', 'ワ']
        }

    def _get_regex(self):
        if self.language == 'ja':
            return self.cj_regex
        elif self.language == 'zh':
            return self.kanji_regex
        elif self.language == 'ko':
            return re.compile(r'[\uAC00-\uD7AF]')
        elif self.language == 'ar':
            return re.compile(r'[\u0600-\u06FF\u0750-\u077F\u08A0-\u08FF\uFB50-\uFDFF\uFE70-\uFEFF]')
        elif self.language == 'ru':
            return re.compile(r'[\u0400-\u04FF\u0500-\u052F\u2DE0-\u2DFF\uA640-\uA69F\u1C80-\u1C8F]')
        elif self.language == 'el':
            return re.compile(r'[\u0370-\u03FF\u1F00-\u1FFF]')
        elif self.language == 'he':
            return re.compile(r'[\u0590-\u05FF\uFB1D-\uFB4F]')
        elif self.language == 'th':
            return re.compile(r'[\u0E00-\u0E7F]')
        else:
            # Latin Extended regex for many European languages/English
            return re.compile(
            r'[a-zA-Z\u00C0-\u00FF\u0100-\u017F\u0180-\u024F\u0250-\u02AF\u1D00-\u1D7F\u1D80-\u1DBF\u1E00-\u1EFF\u2C60-\u2C7F\uA720-\uA7FF\uAB30-\uAB6F]')

    def _get_manual_regex_filter(self):
        manual_regex_filter = config.get_general('screen_capture_regex_filter')
        if manual_regex_filter:
            try:
                return re.compile(manual_regex_filter)
            except re.error as e:
                logger.warning(f'Invalid screen capture regex filter: {e}')
        return None

    def _convert_small_kana_to_big(self, text):
        converted_text = ''.join(self.kana_variants.get(char, [char])[-1] for char in text)
        return converted_text

    def get_line_text(self, line):
        if line.text is not None:
            return line.text
        text_parts = []
        for w in line.words:
            text_parts.append(w.text)
            if w.separator is not None:
                text_parts.append(w.separator)
            else:
                text_parts.append(' ')
        return ''.join(text_parts).strip()

    def _normalize_line_for_comparison(self, line_text):
        if not line_text.replace('\n', ''):
            return ''
        filtered_text = ''.join(self.regex.findall(line_text))
        if self.language == 'ja':
            filtered_text = self._convert_small_kana_to_big(filtered_text)
        return filtered_text

    def find_changed_lines(self, pil_image, current_result):
        if self.frame_stabilization == 0:
            changed_lines = self._find_changed_lines_impl(current_result, self.last_frame_data[1])
            if changed_lines == None:
                return 0, 0, None
            changed_lines_count = len(changed_lines)
            self.last_frame_data = (pil_image, current_result)
            if changed_lines_count and not self.json_output:
                changed_regions_image = self._create_changed_regions_image(pil_image, changed_lines, None, None)
                if not changed_regions_image:
                    logger.warning('Error occurred while creating the differential image')
                    return 0, 0, None
                return changed_lines_count, 0, changed_regions_image
            else:
                return changed_lines_count, 0, None

        changed_lines_stabilization = self._find_changed_lines_impl(current_result, self.last_frame_data[1])
        if changed_lines_stabilization == None:
            return 0, 0, None

        frames_match = len(changed_lines_stabilization) == 0

        logger.debug(f"Frames match: '{frames_match}'")

        if frames_match:
            if self.processed_stable_frame:
                return 0, 0, None
            if time.time() - self.frame_stabilization_timestamp < self.frame_stabilization:
                return 0, 0, None
            changed_lines = self._find_changed_lines_impl(current_result, self.stable_frame_data)
            if self.line_recovery and self.last_last_frame_data:
                logger.debug('Checking for missed lines')
                recovered_lines = self._find_changed_lines_impl(self.last_last_frame_data[1], self.stable_frame_data, current_result)
                recovered_lines_count = len(recovered_lines) if recovered_lines else 0
            else:
                recovered_lines_count = 0
                recovered_lines = []
            self.processed_stable_frame = True
            self.stable_frame_data = current_result
            changed_lines_count = len(changed_lines)
            if (changed_lines_count or recovered_lines_count) and not self.json_output:
                if recovered_lines:
                    changed_regions_image = self._create_changed_regions_image(pil_image, changed_lines, self.last_last_frame_data[0], recovered_lines)
                else:
                    changed_regions_image = self._create_changed_regions_image(pil_image, changed_lines, None, None)

                if not changed_regions_image:
                    logger.warning('Error occurred while creating the differential image')
                    return 0, 0, None
                return changed_lines_count, recovered_lines_count, changed_regions_image
            else:
                return changed_lines_count, recovered_lines_count, None
        else:
            self.last_last_frame_data = self.last_frame_data
            self.last_frame_data = (pil_image, current_result)
            self.processed_stable_frame = False
            self.frame_stabilization_timestamp = time.time()
            return 0, 0, None

    def _find_changed_lines_impl(self, current_result, previous_result, next_result=None):
        if not current_result:
            return None

        changed_lines = []
        current_lines = []
        previous_lines = []
        current_text = []
        previous_text = []

        for p in current_result.paragraphs:
            current_lines.extend(p.lines)
        if len(current_lines) == 0:
            return None

        for current_line in current_lines:
            current_text_line = self.get_line_text(current_line)
            current_text_line = self._normalize_line_for_comparison(current_text_line)
            current_text.append(current_text_line)
        if all(not current_text_line for current_text_line in current_lines):
            return None

        if previous_result:
            for p in previous_result.paragraphs:
                previous_lines.extend(p.lines)
            if next_result:
                for p in next_result.paragraphs:
                    previous_lines.extend(p.lines)

            for previous_line in previous_lines:
                previous_text_line = self.get_line_text(previous_line)
                previous_text_line = self._normalize_line_for_comparison(previous_text_line)
                previous_text.append(previous_text_line)

        all_previous_text = ''.join(previous_text)

        logger.debug("Previous text: '{}'", previous_text)

        for i, current_text_line in enumerate(current_text):
            if not current_text_line:
                continue

            if not next_result and len(current_text_line) < 3:
                text_similar = current_text_line in previous_text
            else:
                text_similar = current_text_line in all_previous_text

            logger.debug("Current line: '{}' Similar: '{}'", current_text_line, text_similar)

            if not text_similar:
                if next_result:
                    logger.opt(colors=True).debug("<red>Recovered line: '{}'</>", current_text_line)
                changed_lines.append(current_lines[i])

        return changed_lines

    def find_changed_lines_text(self, current_result, two_pass_processing_active, recovered_lines_count):
        frame_stabilization_active = self.frame_stabilization != 0

        if (not frame_stabilization_active) or two_pass_processing_active:
            changed_lines, changed_lines_count = self._find_changed_lines_text_impl(current_result, self.last_frame_text, None, None, recovered_lines_count, True)
            if changed_lines == None:
                return [], 0
            self.last_frame_text = current_result
            return changed_lines, changed_lines_count

        changed_lines_stabilization, changed_lines_stabilization_count = self._find_changed_lines_text_impl(current_result, self.last_frame_text, None, None, 0, False)
        if changed_lines_stabilization == None:
            return [], 0

        frames_match = changed_lines_stabilization_count == 0

        logger.debug(f"Frames match: '{frames_match}'")

        if frames_match:
            if self.processed_stable_frame:
                return [], 0
            if time.time() - self.frame_stabilization_timestamp < self.frame_stabilization:
                return [], 0
            if self.line_recovery and self.last_last_frame_text:
                logger.debug('Checking for missed lines')
                recovered_lines, recovered_lines_count = self._find_changed_lines_text_impl(self.last_last_frame_text, self.stable_frame_text, current_result, None, 0, False)
            else:
                recovered_lines_count = 0
                recovered_lines = []
            changed_lines, changed_lines_count = self._find_changed_lines_text_impl(current_result, self.stable_frame_text, None, recovered_lines, recovered_lines_count, True)
            self.processed_stable_frame = True
            self.stable_frame_text = current_result
            return changed_lines, changed_lines_count
        else:
            self.last_last_frame_text = self.last_frame_text
            self.last_frame_text = current_result
            self.processed_stable_frame = False
            self.frame_stabilization_timestamp = time.time()
            return [], 0

    def _find_changed_lines_text_impl(self, current_result, previous_result, next_result, recovered_lines, recovered_lines_count, regex_filter):
        if recovered_lines:
            current_result = recovered_lines + current_result

        if len(current_result) == 0:
            return None, 0

        changed_lines = []
        current_lines = []
        previous_text = []

        for current_line in current_result:
            current_text_line = self._normalize_line_for_comparison(current_line)
            current_lines.append(current_text_line)
        if all(not current_text_line for current_text_line in current_lines):
            return None, 0

        for prev_line in previous_result:
            prev_text = self._normalize_line_for_comparison(prev_line)
            previous_text.append(prev_text)
        if next_result != None:
            for next_text in next_result:
                previous_text.extend(next_text)

        all_previous_text = ''.join(previous_text)

        logger.opt(colors=True).debug("<magenta>Previous text: '{}'</>", previous_text)

        first = True
        changed_lines_count = 0
        len_recovered_lines = 0 if not recovered_lines else len(recovered_lines)
        for i, current_text in enumerate(current_lines):
            changed_line = current_result[i]

            if changed_line == '\n':
                changed_lines.append(changed_line)
                continue
            if not current_text:
                continue

            if next_result != None and len(current_text) < 3:
                text_similar = current_text in previous_text
            else:
                text_similar = current_text in all_previous_text

            logger.opt(colors=True).debug("<magenta>Current line: '{}' Similar: '{}'</>", changed_line, text_similar)

            if text_similar:
                continue

            if (recovered_lines == None or i - len_recovered_lines < 0) and recovered_lines_count > 0:
                if any(line.startswith(current_text) for j, line in enumerate(current_lines) if i != j):
                    logger.opt(colors=True).debug("<magenta>Skipping recovered line: '{}'</>", changed_line)
                    recovered_lines_count -= 1
                    continue

            if next_result != None:
                logger.opt(colors=True).debug("<red>Recovered line: '{}'</>", changed_line)

            if first and len(current_text) > 3:
                first = False
                # For the first line, check if it contains the end of previous text
                if regex_filter and all_previous_text:
                    overlap = self._find_overlap(all_previous_text, current_text)
                    if overlap and len(current_text) > len(overlap):
                        logger.opt(colors=True).debug("<magenta>Found overlap: '{}'</>", overlap)
                        changed_line = self._cut_at_overlap(changed_line, overlap)
                        logger.opt(colors=True).debug("<magenta>After cutting: '{}'</>", changed_line)

            if regex_filter and self.manual_regex_filter:
                changed_line = self.manual_regex_filter.sub('', changed_line)
            changed_lines.append(changed_line)
            changed_lines_count += 1

        return changed_lines, changed_lines_count

    def _find_overlap(self, previous_text, current_text):
        min_overlap_length = 3
        max_overlap_length = min(len(previous_text), len(current_text))

        for overlap_length in range(max_overlap_length, min_overlap_length - 1, -1):
            previous_end = previous_text[-overlap_length:]
            current_start = current_text[:overlap_length]

            if previous_end == current_start:
                return previous_end

        return None

    def _cut_at_overlap(self, current_line, overlap):
        pattern_parts = []
        for char in overlap:
            if char in self.kana_variants:
                variants = self.kana_variants[char]
                pattern_parts.append(f'[{"".join(variants)}]')
            else:
                pattern_parts.append(re.escape(char))

        overlap_pattern = r'.*?'.join(pattern_parts)
        full_pattern = r'^.*?' + overlap_pattern

        logger.opt(colors=True).debug("<magenta>Cut regex: '{}'</>", full_pattern)

        match = re.search(full_pattern, current_line)
        if match:
            cut_position = match.end()
            return current_line[cut_position:]

        return current_line

    def order_paragraphs_and_lines(self, ocr_result):
        # Extract all lines and determine their orientation
        all_lines = []
        for paragraph in ocr_result.paragraphs:
            for line in paragraph.lines:
                if line.text is None:
                    line.text = self.get_line_text(line)

                if paragraph.writing_direction:
                    is_vertical = paragraph.writing_direction == 'TOP_TO_BOTTOM'
                else:
                    is_vertical = self._is_line_vertical(line, ocr_result.image_properties)

                all_lines.append({
                    'line_obj': line,
                    'is_vertical': is_vertical
                })

        if not all_lines:
            return ocr_result

        # Create new paragraphs
        new_paragraphs = self._create_paragraphs_from_lines(all_lines)

        # Group paragraphs into rows
        rows = self._group_paragraphs_into_rows(new_paragraphs)

        # Reorder paragraphs in each row
        reordered_rows = self._reorder_paragraphs_in_rows(rows)

        # Order rows from top to bottom and flatten
        final_paragraphs = self._flatten_rows_to_paragraphs(reordered_rows)

        return OcrResult(
            image_properties=ocr_result.image_properties,
            engine_capabilities=ocr_result.engine_capabilities,
            paragraphs=final_paragraphs
        )

    def _create_paragraphs_from_lines(self, lines):
        grouped = set()
        all_paragraphs = []

        def _group_lines(is_vertical):
            indices = [i for i, line in enumerate(lines) if (line['is_vertical'] in (is_vertical, None)) and i not in grouped]

            if len(indices) < 2:
                return

            if is_vertical:
                get_start = lambda line: line['line_obj'].bounding_box.top
                get_end = lambda line: line['line_obj'].bounding_box.bottom
            else:
                get_start = lambda line: line['line_obj'].bounding_box.left
                get_end = lambda line: line['line_obj'].bounding_box.right

            components = self._find_connected_components(
                items=[lines[i] for i in indices],
                should_connect=lambda l1, l2: self._should_group_in_same_paragraph(l1, l2, is_vertical),
                get_start_coord=get_start,
                get_end_coord=get_end
            )

            for component in components:
                if len(component) > 1:
                    original_indices = [indices[i] for i in component]
                    paragraph_lines = [lines[i] for i in original_indices]
                    new_paragraph = self._create_paragraph_from_lines(paragraph_lines, is_vertical)
                    all_paragraphs.append(new_paragraph)
                    grouped.update(original_indices)

        _group_lines(True)
        _group_lines(False)

        # Create paragraphs out of ungrouped lines
        ungrouped_lines = [line for i, line in enumerate(lines) if i not in grouped]
        for line in ungrouped_lines:
            new_paragraph = self._create_paragraph_from_lines([line], None)
            all_paragraphs.append(new_paragraph)

        return all_paragraphs

    def _create_paragraph_from_lines(self, lines, is_vertical):
        if len(lines) > 1:
            if is_vertical:
                lines = sorted(lines, key=lambda x: x['line_obj'].bounding_box.right, reverse=True)
            else:
                lines = sorted(lines, key=lambda x: x['line_obj'].bounding_box.top)

            lines = self._merge_overlapping_lines(lines, is_vertical)

            if self.furigana_filter:
                lines = self._furigana_filter(lines, is_vertical)

            line_objs = [l['line_obj'] for l in lines]

            left = min(line.bounding_box.left for line in line_objs)
            right = max(line.bounding_box.right for line in line_objs)
            top = min(line.bounding_box.top for line in line_objs)
            bottom = max(line.bounding_box.bottom for line in line_objs)

            new_bbox = BoundingBox(
                center_x=(left + right) / 2,
                center_y=(top + bottom) / 2,
                width=right - left,
                height=bottom - top
            )

            writing_direction = 'TOP_TO_BOTTOM' if is_vertical else 'LEFT_TO_RIGHT'
        else:
            line_objs = [lines[0]['line_obj']]
            new_bbox = lines[0]['line_obj'].bounding_box
            writing_direction = 'TOP_TO_BOTTOM' if lines[0]['is_vertical'] else 'LEFT_TO_RIGHT'

        paragraph = Paragraph(
            bounding_box=new_bbox,
            lines=line_objs,
            writing_direction=writing_direction
        )

        return paragraph

    def _should_group_in_same_paragraph(self, line1, line2, is_vertical):
        bbox1 = line1['line_obj'].bounding_box
        bbox2 = line2['line_obj'].bounding_box

        if is_vertical:
            vertical_overlap = self._check_vertical_overlap(bbox1, bbox2)
            horizontal_distance = self._calculate_horizontal_distance(bbox1, bbox2)
            line_width = max(bbox1.width, bbox2.width)

            return vertical_overlap > 0.7 and horizontal_distance < line_width * 2
        else:
            horizontal_overlap = self._check_horizontal_overlap(bbox1, bbox2)
            vertical_distance = self._calculate_vertical_distance(bbox1, bbox2)
            line_height = max(bbox1.height, bbox2.height)

            return horizontal_overlap > 0.7 and vertical_distance < line_height * 2

    def _merge_overlapping_lines(self, lines, is_vertical):
        if len(lines) < 2:
            return lines

        merged = []
        used_indices = set()

        for i, current_line in enumerate(lines):
            if i in used_indices:
                continue

            # Start with the current line
            merge_group = [current_line]
            used_indices.add(i)
            last_line_in_group = current_line

            # Check subsequent lines in order
            for j, candidate_line in enumerate(lines[i+1:], i+1):
                if j in used_indices:
                    continue

                # Only check if candidate should merge with the last line in our current group
                if self._should_merge_lines(last_line_in_group, candidate_line, is_vertical):
                    merge_group.append(candidate_line)
                    used_indices.add(j)
                    last_line_in_group = candidate_line  # Update last line for next comparison

            # Merge all lines in the group into one
            if len(merge_group) > 1:
                merged_line = self._merge_multiple_lines(merge_group, is_vertical)
                merged.append(merged_line)
                if self.debug_filtering:
                    logger.opt(colors=True).debug("<green>Merged lines: '{}' vertical: '{}'</>", [self.get_line_text(line['line_obj']) for line in merge_group], is_vertical)
            else:
                merged.append(current_line)

        # try:
        #     if isinstance(last_result, list):
        #         last_text = last_result.copy()
        #     elif last_result and last_result[1] == engine_index:
        #         last_text = last_result[0]
        #     else:
        #         last_text = []
            
        #     if engine and not is_second_ocr:
        #         if self.last_few_results and self.last_few_results.get(engine):
        #             for sublist in self.last_few_results.get(engine, []):
        #                 if sublist:
        #                     for item in sublist:
        #                         if item and item not in last_text:
        #                             last_text.append(item)
        #             self.last_few_results[engine].append(orig_text_filtered)
        #         else:
        #             self.last_few_results[engine] = deque(maxlen=3)
        #             self.last_few_results[engine].append(orig_text_filtered)

        # except Exception as e:
        #     logger.error(f"Error processing last_result {last_result}: {e}")
        #     last_text = []

        # new_blocks = []
        # for idx, block in enumerate(orig_text):
        #     if orig_text_filtered[idx] and (orig_text_filtered[idx] not in last_text):
        #         new_blocks.append(
        #             str(block).strip().replace("BLANK_LINE", "\n"))

        # final_blocks = []
        # if self.accurate_filtering:
        #     detection_results = self.pipe(new_blocks, top_k=3, truncation=True)
        #     for idx, block in enumerate(new_blocks):
        #         for result in detection_results[idx]:
        #             if result['label'] == lang:
        #                 final_blocks.append(block)
        #                 break
        # else:
        #     for block in new_blocks:
        #         # This only filters out NON JA/ZH from text when lang is JA/ZH
        #         if lang not in ["ja", "zh"] or self.classify(block)[0] in ['ja', 'zh'] or block == "\n":
        #             final_blocks.append(block)
        return merged

    def _merge_multiple_lines(self, lines, is_vertical):
        if is_vertical:
            # Sort lines by y-coordinate (top to bottom)
            sort_key = lambda line: line['line_obj'].bounding_box.center_y
        else:
            # Sort lines by x-coordinate (left to right)
            sort_key = lambda line: line['line_obj'].bounding_box.center_x

        lines = sorted(lines, key=sort_key)

        text_sorted = ''
        for line in lines:
            text_sorted += line['line_obj'].text

        words_sorted = []
        for line in lines:
            words_sorted.extend(line['line_obj'].words)

        # Calculate new bounding box that encompasses all lines
        bboxes = [line['line_obj'].bounding_box for line in lines]

        left = min(bbox.left for bbox in bboxes)
        right = max(bbox.right for bbox in bboxes)
        top = min(bbox.top for bbox in bboxes)
        bottom = max(bbox.bottom for bbox in bboxes)

        new_bbox = BoundingBox(
            center_x=(left + right) / 2,
            center_y=(top + bottom) / 2,
            width=right - left,
            height=bottom - top
        )

        # Create new merged line
        merged_line = Line(
            bounding_box=new_bbox,
            words=words_sorted,
            text=text_sorted
        )

        return {
            'line_obj': merged_line,
            'is_vertical': is_vertical
        }

    def _should_merge_lines(self, line1, line2, is_vertical):
        bbox1 = line1['line_obj'].bounding_box
        bbox2 = line2['line_obj'].bounding_box

        if is_vertical:
            horizontal_overlap = self._check_horizontal_overlap(bbox1, bbox2)
            vertical_overlap = self._check_vertical_overlap(bbox1, bbox2)

            return (horizontal_overlap > 0.7 and
                    vertical_overlap < 0.4)

        else:
            vertical_overlap = self._check_vertical_overlap(bbox1, bbox2)
            horizontal_overlap = self._check_horizontal_overlap(bbox1, bbox2)

            return (vertical_overlap > 0.7 and
                    horizontal_overlap < 0.4)

    def _furigana_filter(self, lines, is_vertical):
        filtered_lines = []

        for line in lines:
            line_text = self.get_line_text(line['line_obj'])
            normalized_line_text = ''.join(self.cj_regex.findall(line_text))
            line['normalized_text'] = normalized_line_text
        if all(not line['normalized_text'] for line in lines):
            return lines

        for i, line in enumerate(lines):
            if i >= len(lines) - 1:
                filtered_lines.append(line)
                continue

            current_line_text = self.get_line_text(line['line_obj'])
            current_line_bbox = line['line_obj'].bounding_box
            next_line = lines[i + 1]
            next_line_text = self.get_line_text(next_line['line_obj'])
            next_line_bbox = next_line['line_obj'].bounding_box

            if not (line['normalized_text'] and next_line['normalized_text']):
                filtered_lines.append(line)
                continue
            has_kanji = self.kanji_regex.search(line['normalized_text'])
            if has_kanji:
                filtered_lines.append(line)
                continue
            next_has_kanji = self.kanji_regex.search(next_line['normalized_text'])
            if not next_has_kanji:
                filtered_lines.append(line)
                continue

            logger.opt(colors=True).debug("<magenta>Furigana check line: '{}' against line: '{}' vertical: '{}'</>", current_line_text, next_line_text, is_vertical)

            if is_vertical:
                min_h_distance = abs(next_line_bbox.width - current_line_bbox.width) / 2
                max_h_distance = next_line_bbox.width + (current_line_bbox.width / 2)
                min_v_overlap = 0.4

                horizontal_distance = current_line_bbox.center_x - next_line_bbox.center_x
                vertical_overlap = self._check_vertical_overlap(current_line_bbox, next_line_bbox)

                logger.opt(colors=True).debug(f"<magenta>Vertical position: min h.dist '{min_h_distance:.4f}' max h.dist '{max_h_distance:.4f}' h.dist '{horizontal_distance:.4f}' v.overlap '{vertical_overlap:.4f}'</>")

                passed_position_check = min_h_distance < horizontal_distance < max_h_distance and vertical_overlap > min_v_overlap
            else:
                min_v_distance = abs(next_line_bbox.height - current_line_bbox.height) / 2
                max_v_distance = next_line_bbox.height + (current_line_bbox.height / 2)
                min_h_overlap = 0.4

                vertical_distance = next_line_bbox.center_y - current_line_bbox.center_y
                horizontal_overlap = self._check_horizontal_overlap(current_line_bbox, next_line_bbox)

                logger.opt(colors=True).debug(f"<magenta>Horizontal position: min v.dist '{min_v_distance:.4f}' max v.dist '{max_v_distance:.4f}' v.dist '{vertical_distance:.4f}' h.overlap '{horizontal_overlap:.4f}'</>")

                passed_position_check = min_v_distance < vertical_distance < max_v_distance and horizontal_overlap > min_h_overlap

            if not passed_position_check:
                filtered_lines.append(line)
                continue

            if is_vertical:
                width_threshold = next_line_bbox.width * 0.77
                passed_size_check = current_line_bbox.width < width_threshold
                logger.opt(colors=True).debug(f"<magenta>Vertical size (width): kanji '{next_line_bbox.width:.4f}' kana '{current_line_bbox.width:.4f}' max kana '{width_threshold:.4f}'</>")
            else:
                height_threshold = next_line_bbox.height * 0.85
                passed_size_check = current_line_bbox.height < height_threshold
                logger.opt(colors=True).debug(f"<magenta>Horizontal size (height): kanji '{next_line_bbox.height:.4f}' kana '{current_line_bbox.height:.4f}' max kana '{height_threshold:.4f}'</>")

            if not passed_size_check:
                filtered_lines.append(line)
                continue

            logger.opt(colors=True).debug("<yellow>Skipping furigana line: '{}' next to line: '{}'</>", current_line_text, next_line_text)

        return filtered_lines

    def _group_paragraphs_into_rows(self, paragraphs):
        if len(paragraphs) < 2:
            return [{'paragraphs': paragraphs, 'is_vertical': False}]

        components = self._find_connected_components(
            items=paragraphs,
            should_connect=lambda p1, p2: self._check_vertical_overlap(p1.bounding_box, p2.bounding_box) > 0.4,
            get_start_coord=lambda p: p.bounding_box.top,
            get_end_coord=lambda p: p.bounding_box.bottom
        )

        rows = []
        for component in components:
            row_paragraphs = [paragraphs[i] for i in component]
            vertical_count = sum(1 for p in row_paragraphs if p.writing_direction == 'TOP_TO_BOTTOM')
            is_vertical = vertical_count * 2 >= len(row_paragraphs)

            rows.append({
                'paragraphs': row_paragraphs,
                'is_vertical': is_vertical
            })

        return rows

    def _reorder_paragraphs_in_rows(self, rows):
        reordered_rows = []

        for row in rows:
            paragraphs = row['paragraphs']
            is_vertical = row['is_vertical']

            if len(paragraphs) < 2:
                reordered_rows.append(row)
                continue

            # Sort paragraphs by x-coordinate (left edge)
            paragraphs_sorted = sorted(paragraphs, key=lambda p: p.bounding_box.left)

            if is_vertical:
                # Reverse the entire order for predominantly vertical rows
                paragraphs_sorted.reverse()

            # Further reorder contiguous blocks with different orientation
            final_order = self._reorder_mixed_orientation_blocks(paragraphs_sorted, is_vertical)

            reordered_rows.append({
                'paragraphs': final_order,
                'is_vertical': is_vertical
            })

        return reordered_rows

    def _reorder_mixed_orientation_blocks(self, paragraphs, row_is_vertical):
        if len(paragraphs) < 2:
            return paragraphs

        result = []
        current_block = [paragraphs[0]]
        current_orientation = paragraphs[0].writing_direction == 'TOP_TO_BOTTOM'

        for para in paragraphs[1:]:
            para_orientation = para.writing_direction == 'TOP_TO_BOTTOM'

            if para_orientation == current_orientation:
                current_block.append(para)
            else:
                # Process the completed block
                if current_orientation != row_is_vertical:
                    # Reverse blocks that don't match row orientation
                    current_block.reverse()
                result.extend(current_block)

                # Start new block
                current_block = [para]
                current_orientation = para_orientation

        # Process the last block
        if current_orientation != row_is_vertical:
            current_block.reverse()
        result.extend(current_block)

        return result

    def _flatten_rows_to_paragraphs(self, rows):
        rows_sorted = sorted(rows, key=lambda r: min(p.bounding_box.top for p in r['paragraphs']))

        if self.debug_filtering:
            for r in rows_sorted:
                logger.opt(colors=True).debug("<green>Row vertical: '{}'</>", r['is_vertical'])
                for p in r['paragraphs']:
                    logger.opt(colors=True).debug("<green>    Paragraph: '{}' vertical: '{}'</>", [self.get_line_text(line) for line in p.lines], p.writing_direction == 'TOP_TO_BOTTOM')

        all_paragraphs = []
        for row in rows_sorted:
            all_paragraphs.extend(row['paragraphs'])

        return all_paragraphs

    def _calculate_horizontal_distance(self, bbox1, bbox2):
        if bbox1.right < bbox2.left:
            return bbox2.left - bbox1.right
        elif bbox2.right < bbox1.left:
            return bbox1.left - bbox2.right
        else:
            return 0.0

    def _calculate_vertical_distance(self, bbox1, bbox2):
        if bbox1.bottom < bbox2.top:
            return bbox2.top - bbox1.bottom
        elif bbox2.bottom < bbox1.top:
            return bbox1.top - bbox2.bottom
        else:
            return 0.0

    def _is_line_vertical(self, line, image_properties):
        # For very short lines (less than 3 characters), undefined orientation
        if len(self.get_line_text(line)) < 3:
            return None

        bbox = line.bounding_box
        pixel_width = bbox.width * image_properties.width
        pixel_height = bbox.height * image_properties.height

        aspect_ratio = pixel_width / pixel_height
        return aspect_ratio < 0.8

    def _check_horizontal_overlap(self, bbox1, bbox2):
        left1 = bbox1.left
        right1 = bbox1.right
        left2 = bbox2.left
        right2 = bbox2.right

        overlap_left = max(left1, left2)
        overlap_right = min(right1, right2)

        if overlap_right <= overlap_left:
            return 0.0

        overlap_width = overlap_right - overlap_left
        smaller_width = min(bbox1.width, bbox2.width)

        return overlap_width / smaller_width if smaller_width > 0 else 0.0

    def _check_vertical_overlap(self, bbox1, bbox2):
        top1 = bbox1.top
        bottom1 = bbox1.bottom
        top2 = bbox2.top
        bottom2 = bbox2.bottom

        overlap_top = max(top1, top2)
        overlap_bottom = min(bottom1, bottom2)

        if overlap_bottom <= overlap_top:
            return 0.0

        overlap_height = overlap_bottom - overlap_top
        smaller_height = min(bbox1.height, bbox2.height)

        return overlap_height / smaller_height if smaller_height > 0 else 0.0

    def _find_connected_components(self, items, should_connect, get_start_coord, get_end_coord):
        # Build graph using sweep-line algorithm
        graph = {i: [] for i in range(len(items))}

        # Sort items by appropriate coordinate for sweep-line
        sorted_items = sorted(
            [(i, items[i]) for i in range(len(items))],
            key=lambda x: get_start_coord(x[1])
        )

        active_items = []  # (index, item, end_coordinate)

        for original_idx, item in sorted_items:
            current_start = get_start_coord(item)
            line_end = get_end_coord(item)

            # Remove items that are no longer overlapping
            active_items = [
                (active_idx, active_item, active_end) 
                for active_idx, active_item, active_end in active_items
                if active_end > current_start  # Still overlapping
            ]

            # Check current item against all active items
            for active_idx, active_item, _ in active_items:
                if should_connect(item, active_item):
                    graph[original_idx].append(active_idx)
                    graph[active_idx].append(original_idx)

            # Add current item to active list
            active_items.append((original_idx, item, line_end))

        # Find connected components using BFS
        visited = set()
        connected_components = []

        for i in range(len(items)):
            if i not in visited:
                component = []
                queue = collections.deque([i])
                visited.add(i)
                while queue:
                    node = queue.popleft()
                    component.append(node)
                    for neighbor in graph[node]:
                        if neighbor not in visited:
                            visited.add(neighbor)
                            queue.append(neighbor)
                connected_components.append(component)

        return connected_components

    def _create_changed_regions_image(self, pil_image, changed_lines, pil_image_2, changed_lines_2, margin=5):
        def crop_image(image, lines):
            img_width, img_height = image.size

            regions = []
            for line in lines:
                bbox = line.bounding_box
                x1 = (bbox.center_x - bbox.width/2) * img_width - margin
                y1 = (bbox.center_y - bbox.height/2) * img_height - margin
                x2 = (bbox.center_x + bbox.width/2) * img_width + margin
                y2 = (bbox.center_y + bbox.height/2) * img_height + margin

                x1 = max(0, int(x1))
                y1 = max(0, int(y1))
                x2 = min(img_width, int(x2))
                y2 = min(img_height, int(y2))

                if x2 > x1 and y2 > y1:
                    regions.append((x1, y1, x2, y2))

            if not regions:
                return None

            overall_x1 = min(x1 for x1, y1, x2, y2 in regions)
            overall_y1 = min(y1 for x1, y1, x2, y2 in regions)
            overall_x2 = max(x2 for x1, y1, x2, y2 in regions)
            overall_y2 = max(y2 for x1, y1, x2, y2 in regions)

            return image.crop((overall_x1, overall_y1, overall_x2, overall_y2))

        # Handle the case where changed_lines is empty and previous_result is provided
        if (not pil_image) and pil_image_2:
            cropped_2 = crop_image(pil_image_2, changed_lines_2)
            return cropped_2

        # Handle the case where both current and previous results are present
        elif pil_image and pil_image_2:
            # Crop both images
            cropped_1 = crop_image(pil_image, changed_lines)
            cropped_2 = crop_image(pil_image_2, changed_lines_2)

            if cropped_1 is None and cropped_2 is None:
                return None
            elif cropped_1 is None:
                return cropped_2
            elif cropped_2 is None:
                return cropped_1

            # Stitch vertically with previous_result on top
            total_width = max(cropped_1.width, cropped_2.width)
            total_height = cropped_1.height + cropped_2.height

            # Create a new image with white background
            stitched_image = Image.new('RGB', (total_width, total_height), 'white')

            # Paste previous (top) and current (bottom) images, centered horizontally
            prev_x_offset = (total_width - cropped_2.width) // 2
            stitched_image.paste(cropped_2, (prev_x_offset, 0))

            curr_x_offset = (total_width - cropped_1.width) // 2
            stitched_image.paste(cropped_1, (curr_x_offset, cropped_2.height))

            return stitched_image
        elif pil_image:
            return crop_image(pil_image, changed_lines)
        else:
            return None


class ScreenshotThread(threading.Thread):
    def __init__(self, gsm_ocr_config):
        super().__init__(daemon=True)
        screen_capture_area = config.get_general('screen_capture_area')
        self.coordinate_selector_combo_enabled = config.get_general('coordinate_selector_combo') != ''
        self.macos_window_tracker_instance = None
        self.windows_window_tracker_instance = None
        self.window_active = True
        self.window_visible = True
        self.window_closed = False
        self.window_size = None
        self.ocr_config = gsm_ocr_config

        if screen_capture_area == '':
            self.screencapture_mode = 0
        elif screen_capture_area.startswith('screen_'):
            parts = screen_capture_area.split('_')
            if len(parts) != 2 or not parts[1].isdigit():
                exit_with_error('Invalid screen_capture_area')
            screen_capture_monitor = int(parts[1])
            self.screencapture_mode = 1
        elif len(screen_capture_area.split(',')) == 4:
            self.screencapture_mode = 3
        else:
            self.screencapture_mode = 2
            self.screen_capture_window = screen_capture_area
        if self.screen_capture_window:
            self.screencapture_mode = 2

        if self.coordinate_selector_combo_enabled:
            self.launch_coordinate_picker(True, False)

        if self.screencapture_mode != 2:
            self.sct = mss.mss()

            if self.screencapture_mode == 1:
                mon = self.sct.monitors
                if len(mon) <= screen_capture_monitor:
                    exit_with_error('Invalid monitor number in screen_capture_area')
                coord_left = mon[screen_capture_monitor]['left']
                coord_top = mon[screen_capture_monitor]['top']
                coord_width = mon[screen_capture_monitor]['width']
                coord_height = mon[screen_capture_monitor]['height']
            elif self.screencapture_mode == 3:
                coord_left, coord_top, coord_width, coord_height = [
                    int(c.strip()) for c in screen_capture_area.split(',')]
            else:
                self.launch_coordinate_picker(False, True)

            if self.screencapture_mode != 0:
                self.sct_params = {'top': coord_top, 'left': coord_left, 'width': coord_width, 'height': coord_height}
                logger.info(f'Selected coordinates: {coord_left},{coord_top},{coord_width},{coord_height}')
        else:
            self.screen_capture_only_active_windows = config.get_general('screen_capture_only_active_windows')
            self.window_area_coordinates = None

            if sys.platform == 'darwin':
                if config.get_general('screen_capture_old_macos_api') or int(platform.mac_ver()[0].split('.')[0]) < 14:
                    self.old_macos_screenshot_api = True
                else:
                    self.old_macos_screenshot_api = False
                    self.window_stream_configuration = None
                    self.window_content_filter = None
                    self.screencapturekit_queue = queue.Queue()
                    CGMainDisplayID()
                window_list = CGWindowListCopyWindowInfo(
                    kCGWindowListExcludeDesktopElements, kCGNullWindowID)
                window_titles = []
                window_ids = []
                window_index = None
                for i, window in enumerate(window_list):
                    window_title = window.get(kCGWindowName, '')
                    if psutil.Process(window['kCGWindowOwnerPID']).name() not in ('Terminal', 'iTerm2'):
                        window_titles.append(window_title)
                        window_ids.append(window['kCGWindowNumber'])

                if screen_capture_window in window_titles:
                    window_index = window_titles.index(screen_capture_window)
                else:
                    for t in window_titles:
                        if screen_capture_window in t:
                            window_index = window_titles.index(t)
                            break

                if not window_index:
                    exit_with_error('"screen_capture_area" must be empty, "screen_N" where N is a screen number starting from 1, a valid set of coordinates, or a valid window name')

                self.window_id = window_ids[window_index]
                window_title = window_titles[window_index]

                if get_ocr_requires_open_window():
                    self.macos_window_tracker_instance = threading.Thread(
                        target=self.macos_window_tracker)
                    self.macos_window_tracker_instance.start()
                logger.info(f'Selected window: {window_title}')
            elif sys.platform == 'win32':
                self.window_handle, window_title = self.get_windows_window_handle(
                    screen_capture_window)

                if not self.window_handle:
                    exit_with_error('"screen_capture_area" must be empty, "screen_N" where N is a screen number starting from 1, a valid set of coordinates, or a valid window name')

                ctypes.windll.shcore.SetProcessDpiAwareness(2)
                self.window_visible = not win32gui.IsIconic(self.window_handle)
                self.windows_window_mfc_dc = None
                self.windows_window_save_dc = None
                self.windows_window_save_bitmap = None

                self.windows_window_tracker_instance = threading.Thread(
                    target=self.windows_window_tracker)
                self.windows_window_tracker_instance.start()
                logger.info(f'Selected window: {window_title}')
            else:
                exit_with_error('Window capture is only currently supported on Windows and macOS')

            screen_capture_window_area = config.get_general('screen_capture_window_area')
            if screen_capture_window_area != 'window':
                if len(screen_capture_window_area.split(',')) == 4:
                    x, y, x2, y2 = [int(c.strip()) for c in screen_capture_window_area.split(',')]
                    logger.info(f'Selected window coordinates: {x},{y},{x2},{y2}')
                    self.window_area_coordinates = (x, y, x2, y2)
                elif screen_capture_window_area == '':
                    self.launch_coordinate_picker(False, False)
                else:
                    exit_with_error('"screen_capture_window_area" must be empty, "window" for the whole window, or a valid set of coordinates')

    def get_windows_window_handle(self, window_title):
        def callback(hwnd, window_title_part):
            window_title = win32gui.GetWindowText(hwnd)
            if window_title_part in window_title:
                handles.append((hwnd, window_title))
            return True

        handle = win32gui.FindWindow(None, window_title)
        if handle:
            return (handle, window_title)

        handles = []
        win32gui.EnumWindows(callback, window_title)
        for handle in handles:
            _, pid = win32process.GetWindowThreadProcessId(handle[0])
            if psutil.Process(pid).name().lower() not in ('cmd.exe', 'powershell.exe', 'windowsterminal.exe'):
                return handle

        return (None, None)

    def windows_window_tracker(self):
        found = True
        while not terminated.is_set():
            found = win32gui.IsWindow(self.window_handle)
            if not found:
                break
            if self.screen_capture_only_active_windows:
                self.window_active = self.window_handle == win32gui.GetForegroundWindow()
            self.window_visible = not win32gui.IsIconic(self.window_handle)
            time.sleep(0.5)
        if not found:
            self.window_closed = True

    def capture_macos_window_screenshot(self, window_id):
        def shareable_content_completion_handler(shareable_content, error):
            if error:
                self.screencapturekit_queue.put(None)
                return

            target_window = None
            for window in shareable_content.windows():
                if window.windowID() == window_id:
                    target_window = window
                    break

            self.screencapturekit_queue.put(target_window)

        def capture_image_completion_handler(image, error):
            if error:
                self.screencapturekit_queue.put(None)
                return

            with objc.autorelease_pool():
                try:
                    width = CGImageGetWidth(image)
                    height = CGImageGetHeight(image)
                    raw_data = CGDataProviderCopyData(CGImageGetDataProvider(image))
                    bpr = CGImageGetBytesPerRow(image)
                    img = Image.frombuffer('RGBA', (width, height), bytes(raw_data), 'raw', 'BGRA', bpr, 1)
                    self.screencapturekit_queue.put(img)
                except:
                    self.screencapturekit_queue.put(None)

        window_list = CGWindowListCopyWindowInfo(kCGWindowListOptionIncludingWindow, window_id)
        if not window_list or len(window_list) == 0:
            return None
        window_info = window_list[0]
        bounds = window_info.get('kCGWindowBounds')
        if not bounds:
            return None

        width = bounds['Width']
        height = bounds['Height']
        current_size = (width, height)

        if self.window_size != current_size:
            SCShareableContent.getShareableContentWithCompletionHandler_(
                shareable_content_completion_handler
            )

            try:
                result = self.screencapturekit_queue.get(timeout=0.5)
            except queue.Empty:
                return None
            if not result:
                return None

            if self.window_content_filter:
                self.window_content_filter.dealloc()
            self.window_content_filter = SCContentFilter.alloc().initWithDesktopIndependentWindow_(result)

        if not self.window_stream_configuration:
            self.window_stream_configuration = SCStreamConfiguration.alloc().init()
            self.window_stream_configuration.setShowsCursor_(False)
            self.window_stream_configuration.setCaptureResolution_(SCCaptureResolutionNominal)
            self.window_stream_configuration.setIgnoreGlobalClipSingleWindow_(True)

        if self.window_size != current_size:
            self.window_stream_configuration.setSourceRect_(CGRectMake(0, 0, width, height))
            self.window_stream_configuration.setWidth_(width)
            self.window_stream_configuration.setHeight_(height)

        SCScreenshotManager.captureImageWithFilter_configuration_completionHandler_(
            self.window_content_filter, self.window_stream_configuration, capture_image_completion_handler
        )

        try:
            return self.screencapturekit_queue.get(timeout=5)
        except queue.Empty:
            return None

    def macos_window_tracker(self):
        found = True
        while found and not terminated.is_set():
            found = False
            is_active = False
            with objc.autorelease_pool():
                window_list = CGWindowListCopyWindowInfo(
                    kCGWindowListOptionOnScreenOnly, kCGNullWindowID)
                for i, window in enumerate(window_list):
                    if found and window.get(kCGWindowName, '') == 'Fullscreen Backdrop':
                        is_active = True
                        break
                    if self.window_id == window['kCGWindowNumber']:
                        found = True
                        if i == 0 or window_list[i-1].get(kCGWindowName, '') in ('Dock', 'Color Enforcer Window'):
                            is_active = True
                            break
                if not found:
                    window_list = CGWindowListCreateDescriptionFromArray(
                        [self.window_id])
                    if len(window_list) > 0:
                        found = True
            if found:
                self.window_active = is_active
            time.sleep(0.5)
        if not found:
            self.window_closed = True

    def take_screenshot(self, ignore_active_status):
        if self.screencapture_mode == 2:
            if self.window_closed:
                return False
            if not ignore_active_status and not self.window_active:
                return None
            if not self.window_visible:
                return None
            if sys.platform == 'darwin':
                with objc.autorelease_pool():
                    if self.old_macos_screenshot_api:
                        try:
                            cg_image = CGWindowListCreateImageFromArray(CGRectNull, [self.window_id], kCGWindowImageBoundsIgnoreFraming | kCGWindowImageNominalResolution)
                            width = CGImageGetWidth(cg_image)
                            height = CGImageGetHeight(cg_image)
                            raw_data = CGDataProviderCopyData(CGImageGetDataProvider(cg_image))
                            bpr = CGImageGetBytesPerRow(cg_image)
                            img = Image.frombuffer('RGBA', (width, height), bytes(raw_data), 'raw', 'BGRA', bpr, 1)
                        except:
                            img = None
                    else:
                        img = self.capture_macos_window_screenshot(self.window_id)
                if not img:
                    return False
            else:
                try:
                    coord_left, coord_top, right, bottom = win32gui.GetWindowRect(self.window_handle)
                    coord_width = right - coord_left
                    coord_height = bottom - coord_top

                    current_size = (coord_width, coord_height)
                    if self.window_size != current_size:
                        self.cleanup_window_screen_capture()
                        hwnd_dc = win32gui.GetWindowDC(self.window_handle)
                        self.windows_window_mfc_dc = win32ui.CreateDCFromHandle(hwnd_dc)
                        self.windows_window_save_dc = self.windows_window_mfc_dc.CreateCompatibleDC()
                        self.windows_window_save_bitmap = win32ui.CreateBitmap()
                        self.windows_window_save_bitmap.CreateCompatibleBitmap(self.windows_window_mfc_dc, coord_width, coord_height)
                        self.windows_window_save_dc.SelectObject(self.windows_window_save_bitmap)
                        win32gui.ReleaseDC(self.window_handle, hwnd_dc)

                    result = ctypes.windll.user32.PrintWindow(self.window_handle, self.windows_window_save_dc.GetSafeHdc(), 2)
                    bmpinfo = self.windows_window_save_bitmap.GetInfo()
                    bmpstr = self.windows_window_save_bitmap.GetBitmapBits(True)
                    img = Image.frombuffer('RGB', (bmpinfo['bmWidth'], bmpinfo['bmHeight']), bmpstr, 'raw', 'BGRX', 0, 1)
                except pywintypes.error:
                    return False
            window_size_changed = False
            if self.window_size != img.size:
                if self.window_size:
                    window_size_changed = True
                self.window_size = img.size
            if self.window_area_coordinates:
                if window_size_changed:
                    self.window_area_coordinates = None
                    logger.warning('Window size changed, discarding area selection')
                else:
                    img = img.crop(self.window_area_coordinates)
        else:
            sct_img = self.sct.grab(self.sct_params)
            img = Image.frombytes('RGB', sct_img.size, sct_img.bgra, 'raw', 'BGRX')

        return img

    def cleanup_window_screen_capture(self):
        if sys.platform == 'win32':
            try:
                if self.windows_window_save_bitmap:
                    win32gui.DeleteObject(self.windows_window_save_bitmap.GetHandle())
                    self.windows_window_save_bitmap = None
            except:
                pass
            try:
                if self.windows_window_save_dc:
                    self.windows_window_save_dc.DeleteDC()
                    self.windows_window_save_dc = None
            except:
                pass
            try:
                if self.windows_window_mfc_dc:
                    self.windows_window_mfc_dc.DeleteDC()
                    self.windows_window_mfc_dc = None
            except:
                pass
        elif not self.old_macos_screenshot_api:
            if self.window_stream_configuration:
                self.window_stream_configuration.dealloc()
                self.window_stream_configuration = None
            if self.window_content_filter:
                self.window_content_filter.dealloc()
                self.window_content_filter = None

    def write_result(self, result, is_combo):
        if is_combo:
            image_queue.put((result, True))
        else:
            periodic_screenshot_queue.put(result)

    def launch_coordinate_picker(self, init, must_return):
        if init:
            logger.info('Preloading coordinate picker')
            get_screen_selection(True, True)
            return
        if self.screencapture_mode != 2:
            logger.info('Launching screen coordinate picker')
            screen_selection = get_screen_selection(None, self.coordinate_selector_combo_enabled)
            if not screen_selection:
                if on_init:
                    exit_with_error('Picker window was closed or an error occurred')
                else:
                    logger.warning('Picker window was closed or an error occurred, leaving settings unchanged')
                    return
            screen_capture_monitor = screen_selection['monitor']
            x, y, coord_width, coord_height = screen_selection['coordinates']
            if coord_width > 0 and coord_height > 0:
                coord_top = screen_capture_monitor['top'] + y
                coord_left = screen_capture_monitor['left'] + x
            else:
                logger.info('Selection is empty, selecting whole screen')
                coord_left = screen_capture_monitor['left']
                coord_top = screen_capture_monitor['top']
                coord_width = screen_capture_monitor['width']
                coord_height = screen_capture_monitor['height']
            self.sct_params = {'top': coord_top, 'left': coord_left, 'width': coord_width, 'height': coord_height}
            logger.info(f'Selected coordinates: {coord_left},{coord_top},{coord_width},{coord_height}')
        else:
            self.window_area_coordinates = None
            logger.info('Launching window coordinate picker')
            img = self.take_screenshot(True)
            if not img:
                window_selection = False
            else:
                window_selection = get_screen_selection(img, self.coordinate_selector_combo_enabled)
            if not window_selection:
                logger.warning('Picker window was closed or an error occurred, selecting whole window')
            else:
                x, y, coord_width, coord_height = window_selection['coordinates']
                if coord_width > 0 and coord_height > 0:
                    x2 = x + coord_width
                    y2 = y + coord_height
                    logger.info(f'Selected window coordinates: {x},{y},{x2},{y2}')
                    self.window_area_coordinates = (x, y, x2, y2)
                else:
                    logger.info('Selection is empty, selecting whole window')

    def run(self):
        if self.screencapture_mode != 2:
            self.sct = mss.mss()
        while not terminated.is_set():
            if coordinate_selector_event.is_set():
                self.launch_coordinate_picker(False, False)
                coordinate_selector_event.clear()

            try:
                is_combo = screenshot_request_queue.get(timeout=0.5)
            except queue.Empty:
                continue

            img = self.take_screenshot(False)
            img = apply_ocr_config_to_image(img, self.ocr_config)
            self.write_result(img, is_combo)

            if img == False:
                logger.info('The window was closed or an error occurred')
                terminate_handler()
                break

        if self.screencapture_mode == 2:
            self.cleanup_window_screen_capture()
        if self.macos_window_tracker_instance:
            self.macos_window_tracker_instance.join()
        elif self.windows_window_tracker_instance:
            self.windows_window_tracker_instance.join()


    
def apply_adaptive_threshold_filter(img):
    img = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR)
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    inverted = cv2.bitwise_not(gray)
    blur = cv2.GaussianBlur(inverted, (3, 3), 0)
    thresh = cv2.adaptiveThreshold(
        blur, 255, 
        cv2.ADAPTIVE_THRESH_GAUSSIAN_C, 
        cv2.THRESH_BINARY, 
        11, 2
    )
    result = cv2.bitwise_not(thresh)

    return Image.fromarray(result)


def set_last_image(image):
    global last_image, last_image_np
    if image is None:
        last_image = None
        last_image_np = None
    try:
        if image == last_image:
            return
    except Exception:
        last_image = None
        return
    try:
        if last_image is not None and hasattr(last_image, "close"):
            last_image.close()
    except Exception:
        pass
    last_image = image
    last_image_np = np.array(last_image)
    # last_image = apply_adaptive_threshold_filter(image)


def are_images_identical(img1, img2, img2_np=None):
    """
    Compares two images for pixel-wise identity.
    Optionally, pass a cached np.array for img2 as img2_np to avoid repeated conversion.

    Args:
        img1: PIL.Image or np.ndarray
        img2: PIL.Image or np.ndarray
        img2_np: Optional cached np.ndarray for img2

    Returns:
        bool: True if images are identical, False otherwise.
    """
    if any(v is None for v in (img1, img2, img2_np)):
        return False

    try:
        img1_np = np.array(img1)
        img2_np = img2_np if img2_np is not None else np.array(img2)
    except Exception:
        logger.warning("Failed to convert images to numpy arrays for comparison.")
        return False

    return (img1_np.shape == img2_np.shape) and np.array_equal(img1_np, img2_np)


ImageType = Union[np.ndarray, Image.Image]

def _prepare_image(image: ImageType) -> np.ndarray:
    """
    Standardizes an image (PIL or NumPy) into an OpenCV-compatible NumPy array (BGR).
    """
    # If the image is a PIL Image, convert it to a NumPy array
    if isinstance(image, Image.Image):
        # Convert PIL Image (which is RGB) to a NumPy array, then convert RGB to BGR for OpenCV
        prepared_image = cv2.cvtColor(np.array(image), cv2.COLOR_RGB2BGR)
    # If it's already a NumPy array, assume it's in a compatible format (like BGR)
    elif isinstance(image, np.ndarray):
        prepared_image = image
    else:
        raise TypeError(f"Unsupported image type: {type(image)}. Must be a PIL Image or NumPy array.")

    return prepared_image

i = 1

def calculate_ssim_score(imageA: ImageType, imageB: ImageType) -> float:
    global i
    """
    Calculates the structural similarity index (SSIM) between two images.

    Args:
        imageA: The first image as a NumPy array.
        imageB: The second image as a NumPy array.

    Returns:
        The SSIM score between the two images (between -1 and 1).
    """
    
    if isinstance(imageA, Image.Image):
        imageA = apply_adaptive_threshold_filter(imageA)
        
    # Save Images to temp for debugging on a random 1/20 chance
    # if np.random.rand() < 0.05:
    # if i < 600:
    #     # Save as image_000
    #     imageA.save(os.path.join(get_temporary_directory(), f'frame_{i:03d}.png'), 'PNG')
    #     i += 1
        # imageB.save(os.path.join(get_temporary_directory(), f'ssim_imageB_{i:03d}.png'), 'PNG')

    imageA = _prepare_image(imageA)
    imageB = _prepare_image(imageB)

    # Images must have the same dimensions
    if imageA.shape != imageB.shape:
        raise ValueError("Input images must have the same dimensions.")

    # Convert images to grayscale for a more robust SSIM comparison
    # This is less sensitive to minor color changes and lighting.
    # grayA = cv2.cvtColor(imageA, cv2.COLOR_BGR2GRAY)
    # grayB = cv2.cvtColor(imageB, cv2.COLOR_BGR2GRAY)

    # Calculate the SSIM. The `score` is the main value.
    # The `win_size` parameter must be an odd number and less than the image dimensions.
    # We choose a value that is likely to be safe for a variety of image sizes.
    win_size = min(3, imageA.shape[0] // 2, imageA.shape[1] // 2)
    if win_size % 2 == 0:
        win_size -= 1 # ensure it's odd

    score, _ = ssim(imageA, imageB, full=True, win_size=win_size)

    return score



def are_images_similar(imageA: Image.Image, imageB: Image.Image, threshold: float = 0.98) -> bool:
    """
    Compares two images and returns True if their similarity score is above a threshold.

    Args:
        imageA: The first image as a NumPy array.
        imageB: The second image as a NumPy array.
        threshold: The minimum SSIM score to be considered "similar".
                   Defaults to 0.98 (very high similarity). Your original `90` would
                   be equivalent to a threshold of `0.90` here.

    Returns:
        True if the images are similar, False otherwise.
    """
    if None in (imageA, imageB):
        logger.info("One of the images is None, cannot compare.")
        return False
    try:
        score = calculate_ssim_score(imageA, imageB)
    except Exception as e:
        logger.info(e)
        return False
    return score > threshold


def quick_text_detection(pil_image, threshold_ratio=0.01):
    """
    Quick check if image likely contains text using edge detection.
    
    Args:
        pil_image (PIL.Image): Input image
        threshold_ratio (float): Minimum ratio of edge pixels to consider text present
    
    Returns:
        bool: True if text is likely present
    """
    # Convert to grayscale
    gray = np.array(pil_image.convert('L'))
    
    # Apply Canny edge detection
    edges = cv2.Canny(gray, 50, 150)
    
    # Calculate ratio of edge pixels
    edge_ratio = np.sum(edges > 0) / edges.size
    
    return edge_ratio > threshold_ratio


# Use OBS for Screenshot Source (i.e. Linux)
class OBSScreenshotThread(threading.Thread):
    def __init__(self, ocr_config, screen_capture_on_combo, width=1280, height=720, interval=1, is_manual_ocr=False):
        super().__init__(daemon=True)
        self.ocr_config = ocr_config
        self.interval = interval
        self.websocket = None
        self.current_source = None
        self.current_source_name = None
        self.current_scene = None
        self.width = width
        self.height = height
        self.use_periodic_queue = not screen_capture_on_combo
        self.is_manual_ocr = is_manual_ocr

    def write_result(self, result):
        if self.use_periodic_queue:
            periodic_screenshot_queue.put(result)
        else:
            image_queue.put((result, True))
        screenshot_event.clear()

    def connect_obs(self):
        import GameSentenceMiner.obs as obs
        obs.connect_to_obs_sync(check_output=False)
        
    def init_config(self, source=None, scene=None):
        import GameSentenceMiner.obs as obs
        obs.update_current_game()
        current_sources = obs.get_active_video_sources()
        self.current_source = source if source else obs.get_best_source_for_screenshot()
        if not self.current_source:
            time.sleep(1)
            self.init_config(source=source, scene=scene)
            return
        logger.debug(f"Current OBS source: {self.current_source}")
        self.source_width = self.current_source.get(
            "sceneItemTransform").get("sourceWidth") or self.width
        self.source_height = self.current_source.get(
            "sceneItemTransform").get("sourceHeight") or self.height
        if self.source_width and self.source_height and not self.is_manual_ocr and get_ocr_two_pass_ocr():
            self.width, self.height = scale_down_width_height(
                self.source_width, self.source_height)
            logger.info(
                f"Using OBS source dimensions: {self.width}x{self.height}")
        else:
            self.width = self.source_width or 1280
            self.height = self.source_height or 720
            logger.info(
                f"Using source dimensions: {self.width}x{self.height}")
        self.current_source_name = self.current_source.get(
            "sourceName") or None
        if len(current_sources) > 1:
            logger.error(f"Multiple active video sources found in OBS. Using {self.current_source_name} for Screenshot. Please ensure only one source is active for best results.")
        self.current_scene = scene if scene else obs.get_current_game()
        self.ocr_config = get_scene_ocr_config(refresh=True)
        if not self.ocr_config:
            logger.error("No OCR config found for the current scene.")
            return
        self.ocr_config.scale_to_custom_size(self.width, self.height)

    def run(self):
        global last_image
        from PIL import Image
        import GameSentenceMiner.obs as obs

        # Register a scene switch callback in obsws
        def on_scene_switch(scene):
            logger.info(f"Scene switched to: {scene}. Loading new OCR config.")
            self.init_config(scene=scene)

        asyncio.run(obs.register_scene_change_callback(on_scene_switch))

        self.connect_obs()
        self.init_config()
        while not terminated:
            if not screenshot_event.wait(timeout=0.1):
                continue

            if not self.ocr_config:
                logger.info(
                    "No OCR config found for the current scene. Waiting for scene switch.")
                time.sleep(1)
                continue

            if not self.current_source_name:
                obs.update_current_game()
                self.current_source = obs.get_active_source()
                self.current_source_name = self.current_source.get(
                    "sourceName") or None

            try:
                if not self.current_source_name:
                    logger.error(
                        "No active source found in the current scene.")
                    self.write_result(1)
                    continue
                img = obs.get_screenshot_PIL(source_name=self.current_source_name,
                                             width=self.width, height=self.height, img_format='jpg', compression=100)
                
                img = apply_ocr_config_to_image(img, self.ocr_config)

                if img is not None:
                    self.write_result(img)
                else:
                    logger.error("Failed to get screenshot data from OBS.")

            except Exception as e:
                print(e)
                logger.info(
                    f"An unexpected error occurred during OBS Capture : {e}", exc_info=True)
                time.sleep(.5)
                continue
            
def scale_down_width_height(width, height):
        if width == 0 or height == 0:
            return width, height
        # return width, height
        aspect_ratio = width / height
        logger.info(
            f"Scaling down OBS source dimensions: {width}x{height} (Aspect Ratio: {aspect_ratio})")
        if aspect_ratio > 2.66:
            logger.info("Using ultra-wide aspect ratio scaling (32:9).")
            return 1920, 540
        elif aspect_ratio > 2.33:
            logger.info("Using ultra-wide aspect ratio scaling (21:9).")
            return 1920, 800
        elif aspect_ratio > 1.77:
            logger.info("Using standard aspect ratio scaling (16:9).")
            return 1280, 720
        elif aspect_ratio > 1.6:
            logger.info("Using standard aspect ratio scaling (16:10).")
            return 1280, 800
        elif aspect_ratio > 1.33:
            logger.info("Using standard aspect ratio scaling (4:3).")
            return 960, 720
        elif aspect_ratio > 1.25:
            logger.info("Using standard aspect ratio scaling (5:4).")
            return 900, 720
        elif aspect_ratio > 1.5:
            logger.info("Using standard aspect ratio scaling (3:2).")
            return 1080, 720
        else:
            logger.info(
                "Using default aspect ratio scaling (original resolution).")
            return width, height


def apply_ocr_config_to_image(img, ocr_config, is_secondary=False, rectangles=None):
    for rectangle in ocr_config.rectangles:
        if rectangle.is_excluded:
            left, top, width, height = rectangle.coordinates
            draw = ImageDraw.Draw(img)
            draw.rectangle((left, top, left + width, top + height), fill=(0, 0, 0, 0))
            
    if not rectangles:   
        rectangles = [r for r in ocr_config.rectangles if not r.is_excluded and r.is_secondary == is_secondary]
    
    # Sort top to bottom
    if rectangles:
        rectangles.sort(key=lambda r: r.coordinates[1])

    cropped_sections = []
    for rectangle in rectangles:
        area = rectangle.coordinates
        # Ensure crop coordinates are within image bounds
        left = max(0, area[0])
        top = max(0, area[1])
        right = min(img.width, area[0] + area[2])
        bottom = min(img.height, area[1] + area[3])
        crop = img.crop((left, top, right, bottom))
        cropped_sections.append(crop)

    if len(cropped_sections) > 1:
        # Width is the max width of all sections, height is the sum of all sections + gaps
        # Gaps are 50 pixels between sections
        combined_width = max(section.width for section in cropped_sections)
        combined_height = sum(section.height for section in cropped_sections) + (
            len(cropped_sections) - 1) * 50
        combined_img = Image.new("RGBA", (combined_width, combined_height))
        y_offset = 0
        for section in cropped_sections:
            combined_img.paste(section, (0, y_offset))
            y_offset += section.height + 50
        img = combined_img
    elif cropped_sections:
        img = cropped_sections[0]
    return img


class AutopauseTimer:
    def __init__(self):
        self.timeout = config.get_general('auto_pause')
        self.timer_thread = threading.Thread(target=self._countdown, daemon=True)
        self.running = True
        self.countdown_active = threading.Event()
        self.allow_auto_pause = threading.Event()
        self.seconds_remaining = 0
        self.lock = threading.Lock()
        self.timer_thread.start()

    def start_timer(self):
        with self.lock:
            self.seconds_remaining = self.timeout
        self.allow_auto_pause.set()
        self.countdown_active.set()

    def stop_timer(self):
        self.countdown_active.clear()
        self.allow_auto_pause.set()

    def stop(self):
        self.running = False
        self.allow_auto_pause.set()
        self.countdown_active.set()
        if self.timer_thread.is_alive():
            self.timer_thread.join()

    def _countdown(self):
        while self.running:
            self.countdown_active.wait()
            if not self.running:
                break

            while self.running and self.countdown_active.is_set() and self.seconds_remaining > 0:
                time.sleep(1)
                with self.lock:
                    self.seconds_remaining -= 1

            self.allow_auto_pause.wait()

            if self.running and self.countdown_active.is_set() and self.seconds_remaining == 0:
                self.countdown_active.clear()
                if not (paused.is_set() or terminated.is_set()):
                    pause_handler(True)


class SecondPassThread:
    def __init__(self):
        self.input_queue = queue.Queue()
        self.output_queue = queue.Queue()
        self.ocr_thread = None
        self.running = False

    def start(self):
        if self.ocr_thread is None or not self.ocr_thread.is_alive():
            self.running = True
            self.ocr_thread = threading.Thread(target=self._process_ocr, daemon=True)
            self.ocr_thread.start()

    def stop(self):
        self.running = False
        if self.ocr_thread and self.ocr_thread.is_alive():
            self.ocr_thread.join()
        while not self.input_queue.empty():
            self.input_queue.get()
        while not self.output_queue.empty():
            self.output_queue.get()

    def _process_ocr(self):
        while self.running:
            try:
                img, engine_index_local, recovered_lines_count = self.input_queue.get(timeout=0.5)

                engine_instance = engine_instances[engine_index_local]
                start_time = time.time()
                res, result_data = engine_instance(img)
                end_time = time.time()

                self.output_queue.put((engine_instance.readable_name, res, result_data, end_time - start_time, recovered_lines_count))
            except queue.Empty:
                continue

    def submit_task(self, img, engine_instance, recovered_lines_count):
        self.input_queue.put((img, engine_instance, recovered_lines_count))

    def get_result(self):
        try:
            return self.output_queue.get_nowait()
        except queue.Empty:
            return None


class OutputResult:
    def __init__(self):
        self.screen_capture_periodic = config.get_general('screen_capture_delay_secs') != -1
        self.json_output = config.get_general('output_format') == 'json'
        self.engine_color = config.get_general('engine_color')
        self.verbosity = config.get_general('verbosity')
        self.notifications = config.get_general('notifications')
        self.reorder_text = config.get_general('reorder_text')
        self.line_separator = '' if config.get_general('join_lines') else config.get_general('line_separator').encode().decode('unicode_escape') 
        self.paragraph_separator = '' if config.get_general('join_paragraphs') else config.get_general('paragraph_separator').encode().decode('unicode_escape')
        self.write_to = config.get_general('write_to')
        self.filtering = TextFiltering()
        self.second_pass_thread = SecondPassThread()

    def _post_process(self, text, strip_spaces):
        line_separator = '' if strip_spaces else self.line_separator
        paragraphs = []

        current_paragraph = []
        for line in text:
            if line == '\n':
                if current_paragraph:
                    paragraph = line_separator.join(current_paragraph)
                    paragraphs.append(paragraph)
                    current_paragraph = []
                continue
            line = line.replace('…', '...')
            line = re.sub('[・.]{2,}', lambda x: (x.end() - x.start()) * '.', line)
            is_cj_text = self.filtering.cj_regex.search(line)
            if is_cj_text:
                current_paragraph.append(jaconv.h2z(''.join(line.split()), ascii=True, digit=True))
            else:
                current_paragraph.append(re.sub(r'\s+', ' ', line).strip())

        text = self.paragraph_separator.join(paragraphs)
        return text

    def _extract_lines_from_result(self, result_data):
        lines = []
        for p in result_data.paragraphs:
            for l in p.lines:
                lines.append(self.filtering.get_line_text(l))
            lines.append('\n')
        return lines

    def __call__(self, img_or_path, filter_text, auto_pause, notify):
        engine_index_local = engine_index
        engine_instance = engine_instances[engine_index_local]
        two_pass_processing_active = False
        result_data = None

        if filter_text and self.screen_capture_periodic:
            if engine_index_2 != -1 and engine_index_2 != engine_index_local and engine_instance.threading_support:
                two_pass_processing_active = True
                engine_instance_2 = engine_instances[engine_index_2]
                start_time = time.time()
                res2, result_data_2 = engine_instance_2(img_or_path)
                end_time = time.time()

                if not res2:
                    logger.opt(colors=True).warning(f'<{self.engine_color}>{engine_instance_2.readable_name}</> reported an error after {end_time - start_time:0.03f}s: {result_data_2}')
                else:
                    changed_lines_count, recovered_lines_count, changed_regions_image = self.filtering.find_changed_lines(img_or_path, result_data_2)

                    if changed_lines_count or recovered_lines_count:
                        if self.verbosity != 0:
                            logger.opt(colors=True).info(f"<{self.engine_color}>{engine_instance_2.readable_name}</> found {changed_lines_count + recovered_lines_count} changed line(s) in {end_time - start_time:0.03f}s, re-OCRing with <{self.engine_color}>{engine_instance.readable_name}</>")

                        if changed_regions_image:
                            img_or_path = changed_regions_image

                        self.second_pass_thread.start()
                        self.second_pass_thread.submit_task(img_or_path, engine_index_local, recovered_lines_count)

                second_pass_result = self.second_pass_thread.get_result()
                if second_pass_result:
                    engine_name, res, result_data, processing_time, recovered_lines_count = second_pass_result
                else:
                    return
            else:
                self.second_pass_thread.stop()

        if auto_pause_handler and auto_pause:
            auto_pause_handler.allow_auto_pause.clear()

        if not result_data:
            start_time = time.time()
            res, result_data = engine_instance(img_or_path)
            end_time = time.time()
            processing_time = end_time - start_time
            engine_name = engine_instance.readable_name
            recovered_lines_count = 0

        if not res:
            if auto_pause_handler and auto_pause:
                auto_pause_handler.stop_timer()
            logger.opt(colors=True).warning(f'<{self.engine_color}>{engine_name}</> reported an error after {processing_time:0.03f}s: {result_data}')
            return

        if isinstance(result_data, OcrResult):
            if self.reorder_text:
                result_data = self.filtering.order_paragraphs_and_lines(result_data)
            result_data_text = self._extract_lines_from_result(result_data)
        else:
            result_data_text = result_data

        if filter_text:
            changed_lines, changed_lines_count = self.filtering.find_changed_lines_text(result_data_text, two_pass_processing_active, recovered_lines_count)
            if self.screen_capture_periodic and not changed_lines_count:
                if auto_pause_handler and auto_pause:
                    auto_pause_handler.allow_auto_pause.set()
                return
            output_text = self._post_process(changed_lines, True)
        else:
            output_text = self._post_process(result_data_text, False)

        if self.json_output:
            output_string = json.dumps(asdict(result_data), ensure_ascii=False)
        else:
            output_string = output_text

        if self.verbosity != 0:
            if self.verbosity < -1:
                log_message = ': ' + output_text
            elif self.verbosity == -1:
                log_message = ''
            else:
                log_message = ': ' + (output_text if len(output_text) <= self.verbosity else output_text[:self.verbosity] + '[...]')

            logger.opt(colors=True).info(f'Text recognized in {processing_time:0.03f}s using <{self.engine_color}>{engine_name}</>{log_message}')

        if notify and self.notifications:
            notifier.send(title='owocr', message='Text recognized: ' + output_text, urgency=get_notification_urgency())

        if self.write_to == 'websocket':
            websocket_server_thread.send_text(output_string)
        elif self.write_to == 'clipboard':
            pyperclipfix.copy(output_string)
        else:
            with Path(self.write_to).open('a', encoding='utf-8') as f:
                f.write(output_string + '\n')

        if auto_pause_handler and auto_pause:
            if not paused.is_set():
                auto_pause_handler.start_timer()
            else:
                auto_pause_handler.stop_timer()


def get_notification_urgency():
    if sys.platform == 'win32':
        return Urgency.Low
    return Urgency.Normal


def pause_handler(is_combo=True):
    global paused
    message = 'Unpaused!' if paused.is_set() else 'Paused!'

    if auto_pause_handler:
        auto_pause_handler.stop_timer()
    if is_combo:
        notifier.send(title='owocr', message=message, urgency=get_notification_urgency())
    logger.info(message)
    paused.clear() if paused.is_set() else paused.set()


def engine_change_handler(user_input='s', is_combo=True):
    global engine_index
    old_engine_index = engine_index

    if user_input.lower() == 's':
        if engine_index == len(engine_keys) - 1:
            engine_index = 0
        else:
            engine_index += 1
    elif user_input.lower() != '' and user_input.lower() in engine_keys:
        engine_index = engine_keys.index(user_input.lower())
    if engine_index != old_engine_index:
        new_engine_name = engine_instances[engine_index].readable_name
        if is_combo:
            notifier.send(
                title='owocr', message=f'Switched to {new_engine_name}')
        engine_color = config.get_general('engine_color')
        logger.opt(ansi=True).info(
            f'Switched to <{engine_color}>{new_engine_name}</{engine_color}>!')


def engine_change_handler_name(engine, switch=True):
    global engine_index
    old_engine_index = engine_index
    
    if engine not in get_engine_names():
        for _, engine_class in sorted(inspect.getmembers(sys.modules[__name__],
                                                     lambda x: hasattr(x, '__module__') and x.__module__ and (
        __package__ + '.ocr' in x.__module__ or __package__ + '.secret' in x.__module__) and inspect.isclass(
                                                         x))):
            if engine_class.name == engine:
                if config.get_engine(engine_class.name) == None:
                    engine_instance = engine_class()
                else:
                    engine_instance = engine_class(config.get_engine(
                        engine_class.name), lang=get_ocr_language())

                if engine_instance.available:
                    engine_instances.append(engine_instance)
                    engine_keys.append(engine_class.key)

    if switch:
        for i, instance in enumerate(engine_instances):
            if instance.name.lower() in engine.lower():
                engine_index = i
                break

        if engine_index != old_engine_index:
            new_engine_name = engine_instances[engine_index].readable_name
            notifier.send(title='owocr', message=f'Switched to {new_engine_name}')
            engine_color = config.get_general('engine_color')
            logger.opt(ansi=True).info(
                f'Switched to <{engine_color}>{new_engine_name}</{engine_color}>!')


def user_input_thread_run():
    def _terminate_handler():
        global terminated
        logger.info('Terminated!')
        terminated = True
    import sys

    if sys.platform == 'win32':
        import msvcrt
        while not terminated:
            user_input = None
            if msvcrt.kbhit():  # Check if a key is pressed
                user_input_bytes = msvcrt.getch()
                try:
                    user_input = user_input_bytes.decode()
                except UnicodeDecodeError:
                    pass
            if not user_input:  # If no input from msvcrt, check stdin
                import sys
                user_input = sys.stdin.read(1)

                if user_input.lower() in 'tq':
                    _terminate_handler()
                elif user_input.lower() == 'p':
                    pause_handler(False)
                else:
                    engine_change_handler(user_input, False)
    else:
        import tty
        import termios
        notifier.send(title='owocr', message=f'Switched to {new_engine_name}', urgency=get_notification_urgency())
        engine_color = config.get_general('engine_color')
        logger.opt(colors=True).info(f'Switched to <{engine_color}>{new_engine_name}</>!')


def terminate_handler(sig=None, frame=None):
    global terminated
    if not terminated.is_set():
        logger.info('Terminated!')
        terminated.set()


def exit_with_error(error):
    logger.error(error)
    terminate_handler()
    sys.exit(1)


def user_input_thread_run():
    if sys.platform == 'win32':
        import msvcrt
        while not terminated.is_set():
            if coordinate_selector_event.is_set():
                while coordinate_selector_event.is_set():
                    time.sleep(0.1)
            if msvcrt.kbhit():
                try:
                    user_input_bytes = msvcrt.getch()
                    user_input = user_input_bytes.decode()
                    if user_input.lower() in 'tq':
                        terminate_handler()
                    elif user_input.lower() == 'p':
                        pause_handler(False)
                    else:
                        engine_change_handler(user_input, False)
                except UnicodeDecodeError:
                    pass
            else:
                time.sleep(0.2)
    else:
        import termios, select
        fd = sys.stdin.fileno()
        old_settings = termios.tcgetattr(fd)
        new_settings = termios.tcgetattr(fd)
        new_settings[0] &= ~termios.IXON
        new_settings[3] &= ~(termios.ICANON | termios.ECHO)
        new_settings[6][termios.VMIN] = 1
        new_settings[6][termios.VTIME] = 0
        try:
            termios.tcsetattr(fd, termios.TCSANOW, new_settings)
            while not terminated.is_set():
                if coordinate_selector_event.is_set():
                    while coordinate_selector_event.is_set():
                        time.sleep(0.1)
                    termios.tcsetattr(fd, termios.TCSANOW, new_settings)
                rlist, _, _ = select.select([sys.stdin], [], [], 0.2)
                if rlist:
                    user_input = sys.stdin.read(1)
                    if user_input.lower() in 'tq':
                        terminate_handler()
                    elif user_input.lower() == 'p':
                        pause_handler(False)
                    else:
                        engine_change_handler(user_input, False)
        finally:
            termios.tcsetattr(fd, termios.TCSADRAIN, old_settings)


def on_screenshot_combo():
    screenshot_request_queue.put(True)


def on_window_minimized(minimized):
    global screencapture_window_visible
    screencapture_window_visible = not minimized
    

def do_configured_ocr_replacements(text: str) -> str:
    return do_text_replacements(text, OCR_REPLACEMENTS_FILE)


def process_and_write_results(img_or_path, write_to=None, last_result=None, filtering: TextFiltering = None, notify=None, engine=None, ocr_start_time=None, furigana_filter_sensitivity=0):
    global engine_index
    # TODO Replace this at a later date
    is_second_ocr = bool(engine)
    if auto_pause_handler:
        auto_pause_handler.stop()
    if engine:
        for i, instance in enumerate(engine_instances):
            if instance.name.lower() in engine.lower():
                engine_instance = instance
                break
    else:
        engine_instance = engine_instances[engine_index]
        engine = engine_instance.name

    engine_color = config.get_general('engine_color')
    
    start_time = time.time()
    result = engine_instance(img_or_path, furigana_filter_sensitivity)
    res, text, crop_coords = (*result, None)[:3]

    if not res and ocr_2 == engine:
        logger.opt(ansi=True).info(
            f"<{engine_color}>{engine_instance.readable_name}</{engine_color}> failed with message: {text}, trying <{engine_color}>{ocr_1}</{engine_color}>")
        for i, instance in enumerate(engine_instances):
            if instance.name.lower() in ocr_1.lower():
                engine_instance = instance
                if last_result:
                    last_result = []
                break
        start_time = time.time()
        result = engine_instance(img_or_path, furigana_filter_sensitivity)
        res, text, crop_coords = (*result, None)[:3]

    end_time = time.time()

    orig_text = []
    # print(filtering)
    #
    #
    # print(lang)

    # print(last_result)
    # print(engine_index)

    if res:
        if 'provider' in text:
            if write_to == 'callback':
                logger.opt(ansi=True).info(f"{len(text['boxes'])} text boxes recognized in {end_time - start_time:0.03f}s using Meiki:")
                txt_callback('', '', ocr_start_time,
                             img_or_path, is_second_ocr, filtering, text.get('crop_coords', None), meiki_boxes=text.get('boxes', []))
                return str(text), str(text)
        
        if isinstance(text, list):
            for i, line in enumerate(text):
                text[i] = do_configured_ocr_replacements(line)
        else:
            text = do_configured_ocr_replacements(text)
        if filtering:
            text, orig_text = filtering(text, last_result, engine=engine, is_second_ocr=is_second_ocr)
        if get_ocr_language() == "ja" or get_ocr_language() == "zh":
            text = post_process(text, keep_blank_lines=get_ocr_keep_newline())
        if notify and config.get_general('notifications'):
            notifier.send(title='owocr', message='Text recognized: ' + text)
            
        if text and write_to is not None:
            if check_text_is_all_menu(text, crop_coords):
                logger.opt(ansi=True).info('Text is identified as all menu items, skipping further processing.')
                return orig_text, ''
            
        logger.opt(ansi=True).info(
    f'OCR Run {1 if not is_second_ocr else 2}: Text recognized in {end_time - start_time:0.03f}s using <{engine_color}>{engine_instance.readable_name}</{engine_color}>: {text}')

        if write_to == 'websocket':
            websocket_server_thread.send_text(text)
        elif write_to == 'clipboard':
            pyperclipfix.copy(text)
        elif write_to == "callback":
            txt_callback(text, orig_text, ocr_start_time,
                         img_or_path, is_second_ocr, filtering, crop_coords)
        elif write_to:
            with Path(write_to).open('a', encoding='utf-8') as f:
                f.write(text + '\n')

        if auto_pause_handler and not paused:
            auto_pause_handler.start()
    else:
        logger.opt(ansi=True).info(
            f'<{engine_color}>{engine_instance.readable_name}</{engine_color}> reported an error after {end_time - start_time:0.03f}s: {text}')

    # print(orig_text)
    # print(text)

    return orig_text, text

def check_text_is_all_menu(text: str, crop_coords: tuple) -> bool:
    """
    Checks if the recognized text consists entirely of menu items.
    This function checks if the detected text area falls entirely within secondary rectangles (menu areas).

    :param text: The recognized text from OCR.
    :param crop_coords: Tuple containing (x, y, x2, y2) of the detected text area relative to the cropped image.
    :return: True if the text is all menu items (within secondary rectangles), False otherwise.
    """
    if not text or not crop_coords:
        return False

    original_width = obs_screenshot_thread.width
    original_height = obs_screenshot_thread.height
    crop_x, crop_y, crop_x2, crop_y2 = crop_coords

    ocr_config = get_scene_ocr_config()
    
    if not any(rect.is_secondary for rect in ocr_config.rectangles):
        return False

    ocr_config.scale_to_custom_size(original_width, original_height)
    if not ocr_config or not ocr_config.rectangles:
        return False

    primary_rectangles = [rect for rect in ocr_config.rectangles if not rect.is_excluded and not rect.is_secondary]
    menu_rectangles = [rect for rect in ocr_config.rectangles if rect.is_secondary and not rect.is_excluded]

    if not menu_rectangles:
        return False

    if not primary_rectangles:
        if crop_x < 0 or crop_y < 0 or crop_x2 > original_width or crop_y2 > original_height:
            return False
        for menu_rect in menu_rectangles:
            rect_left, rect_top, rect_width, rect_height = menu_rect.coordinates
            rect_right = rect_left + rect_width
            rect_bottom = rect_top + rect_height
            if (crop_x >= rect_left and crop_y >= rect_top and
                crop_x2 <= rect_right and crop_y2 <= rect_bottom):
                return True
        return False

    primary_rectangles.sort(key=lambda r: r.coordinates[1])

    if len(primary_rectangles) == 1:
        primary_rect = primary_rectangles[0]
        primary_left, primary_top, primary_width, primary_height = primary_rect.coordinates
        original_x = crop_x + primary_left
        original_y = crop_y + primary_top
        original_x2 = crop_x2 + primary_left
        original_y2 = crop_y2 + primary_top
    else:
        current_y_offset = 0
        original_x = None
        original_y = None
        original_x2 = None
        original_y2 = None
        for i, primary_rect in enumerate(primary_rectangles):
            primary_left, primary_top, primary_width, primary_height = primary_rect.coordinates
            section_height = primary_height
            if crop_y >= current_y_offset and crop_y < current_y_offset + section_height:
                original_x = crop_x + primary_left
                original_y = (crop_y - current_y_offset) + primary_top
                original_x2 = crop_x2 + primary_left
                original_y2 = crop_y2 + primary_top
                break
            current_y_offset += section_height + 50
        if original_x is None or original_y is None:
            return False

    if original_x < 0 or original_y < 0 or original_x > original_width or original_y > original_height:
        return False

    for menu_rect in menu_rectangles:
        rect_left, rect_top, rect_width, rect_height = menu_rect.coordinates
        rect_right = rect_left + rect_width
        rect_bottom = rect_top + rect_height
        if (original_x >= rect_left and original_y >= rect_top and
            original_x2 <= rect_right and original_y2 <= rect_bottom):
            return True

    return False

def get_path_key(path):
    return path, path.lstat().st_mtime


def init_config(parse_args=True):
    global config
    config = Config(parse_args)

def on_coordinate_selector_combo():
    coordinate_selector_event.set()

def run(read_from=None,
        read_from_secondary=None,
        write_to=None,
        engine=None,
        pause_at_startup=None,
        ignore_flag=None,
        delete_images=None,
        notifications=None,
        auto_pause=0,
        combo_pause=None,
        combo_engine_switch=None,
        screen_capture_area=None,
        screen_capture_areas=None,
        screen_capture_exclusions=None,
        screen_capture_window=None,
        screen_capture_delay_secs=None,
        screen_capture_combo=None,
        stop_running_flag=None,
        screen_capture_event_bus=None,
        text_callback=None,
        monitor_index=None,
        ocr1=None,
        ocr2=None,
        gsm_ocr_config=None,
        furigana_filter_sensitivity=None,
        config_check_thread=None
        ):
    """
    Japanese OCR client

    Runs OCR in the background.
    It can read images copied to the system clipboard or placed in a directory, images sent via a websocket or a Unix domain socket, or directly capture a screen (or a portion of it) or a window.
    Recognized texts can be either saved to system clipboard, appended to a text file or sent via a websocket.

    :param read_from: Specifies where to read input images from. Can be either "clipboard", "websocket", "unixsocket" (on macOS/Linux), "screencapture", or a path to a directory.
    :param write_to: Specifies where to save recognized texts to. Can be either "clipboard", "websocket", or a path to a text file.
    :param delay_secs: How often to check for new images, in seconds.
    :param engine: OCR engine to use. Available: "mangaocr", "glens", "glensweb", "bing", "gvision", "avision", "alivetext", "azure", "winrtocr", "oneocr", "easyocr", "rapidocr", "ocrspace".
    :param pause_at_startup: Pause at startup.
    :param ignore_flag: Process flagged clipboard images (images that are copied to the clipboard with the *ocr_ignore* string).
    :param delete_images: Delete image files after processing when reading from a directory.
    :param notifications: Show an operating system notification with the detected text.
    :param auto_pause: Automatically pause the program after the specified amount of seconds since the last successful text recognition. Will be ignored when reading with screen capture. 0 to disable.
    :param combo_pause: Specifies a combo to wait on for pausing the program. As an example: "<ctrl>+<shift>+p". The list of keys can be found here: https://pynput.readthedocs.io/en/latest/keyboard.html#pynput.keyboard.Key
    :param combo_engine_switch: Specifies a combo to wait on for switching the OCR engine. As an example: "<ctrl>+<shift>+a". To be used with combo_pause. The list of keys can be found here: https://pynput.readthedocs.io/en/latest/keyboard.html#pynput.keyboard.Key
    :param screen_capture_area: Specifies area to target when reading with screen capture. Can be either empty (automatic selector), a set of coordinates (x,y,width,height), "screen_N" (captures a whole screen, where N is the screen number starting from 1) or a window name (the first matching window title will be used).
    :param screen_capture_delay_secs: Specifies the delay (in seconds) between screenshots when reading with screen capture.
    :param screen_capture_only_active_windows: When reading with screen capture and screen_capture_area is a window name, specifies whether to only target the window while it's active.
    :param screen_capture_combo: When reading with screen capture, specifies a combo to wait on for taking a screenshot instead of using the delay. As an example: "<ctrl>+<shift>+s". The list of keys can be found here: https://pynput.readthedocs.io/en/latest/keyboard.html#pynput.keyboard.Key
    """

    if read_from is None:
        read_from = config.get_general('read_from')

    if read_from_secondary is None:
        read_from_secondary = config.get_general('read_from_secondary')

    if screen_capture_area is None:
        screen_capture_area = config.get_general('screen_capture_area')

    # if screen_capture_only_active_windows is None:
    #     screen_capture_only_active_windows = config.get_general('screen_capture_only_active_windows')

    if screen_capture_exclusions is None:
        screen_capture_exclusions = config.get_general(
            'screen_capture_exclusions')

    if screen_capture_window is None:
        screen_capture_window = config.get_general('screen_capture_window')

    if screen_capture_delay_secs is None:
        screen_capture_delay_secs = config.get_general(
            'screen_capture_delay_secs')

    if screen_capture_combo is None:
        screen_capture_combo = config.get_general('screen_capture_combo')

    if stop_running_flag is None:
        stop_running_flag = config.get_general('stop_running_flag')

    if screen_capture_event_bus is None:
        screen_capture_event_bus = config.get_general(
            'screen_capture_event_bus')

    if text_callback is None:
        text_callback = config.get_general('text_callback')

    if write_to is None:
        write_to = config.get_general('write_to')

    logger.configure(
        handlers=[{'sink': sys.stderr, 'format': config.get_general('logger_format')}])


# def run():
#     logger_level = 'DEBUG' if config.get_general('uwu') else 'INFO'
#     logger.configure(handlers=[{'sink': sys.stderr, 'format': config.get_general('logger_format'), 'level': logger_level}])

#     if config.has_config:
#         logger.info('Parsed config file')
#     else:
#         logger.warning('No config file, defaults will be used')
#         if config.downloaded_config:
#             logger.info(
#                 f'A default config file has been downloaded to {config.config_path}')

    global engine_instances
    global engine_keys
    output_format = config.get_general('output_format')
    engines_setting = config.get_general('engines')
    default_engine_setting = config.get_general('engine')
    secondary_engine_setting = config.get_general('engine_secondary')
    language = config.get_general('language')
    engine_instances = []
    config_engines = []
    engine_keys = []
    default_engine = ''
    engine_secondary = ''

    if len(engines_setting) > 0:
        for config_engine in engines_setting.split(','):
            config_engines.append(config_engine.strip().lower())

    for _,engine_class in sorted(inspect.getmembers(sys.modules[__name__], lambda x: hasattr(x, '__module__') and x.__module__ and __package__ + '.ocr' in x.__module__ and inspect.isclass(x) and hasattr(x, 'name'))):
        if len(config_engines) == 0 or engine_class.name in config_engines:

            if output_format == 'json' and not engine_class.coordinate_support:
                logger.warning(f"Skipping {engine_class.readable_name} as it does not support JSON output")
                continue

            if not engine_class.config_entry:
                if engine_class.manual_language:
                    engine_instance = engine_class(language=language)
                else:
                    engine_instance = engine_class()
            else:
                if engine_class.manual_language:
                    engine_instance = engine_class(config=config.get_engine(engine_class.config_entry), language=language)
                else:
                    engine_instance = engine_class(config=config.get_engine(engine_class.config_entry))

            if engine_instance.available:
                engine_instances.append(engine_instance)
                engine_keys.append(engine_class.key)
                if default_engine_setting == engine_class.name:
                    default_engine = engine_class.key
                if secondary_engine_setting == engine_class.name and engine_class.local and engine_class.coordinate_support:
                    engine_secondary = engine_class.key

    if len(engine_keys) == 0:
        exit_with_error('No engines available!')

    if default_engine_setting and not default_engine:
        logger.warning("Couldn't find selected engine, using the first one in the list")

    if secondary_engine_setting and not engine_secondary:
        logger.warning("Couldn't find selected secondary engine, make sure it's enabled, local and has JSON format support. Disabling two pass processing")

    global engine_index
    global engine_index_2
    global terminated
    global paused
    global just_unpaused
    global first_pressed
    global auto_pause_handler
    global notifier
    global websocket_server_thread
    global screenshot_thread
    global obs_screenshot_thread
    global image_queue
    global coordinate_selector_event
    non_path_inputs = ('screencapture', 'clipboard', 'websocket', 'unixsocket', 'obs')
    read_from = config.get_general('read_from')
    read_from_secondary = config.get_general('read_from_secondary')
    read_from_path = None
    read_from_readable = []
    write_to = config.get_general('write_to')
    terminated = threading.Event()
    paused = threading.Event()
    if config.get_general('pause_at_startup'):
        paused.set()
    auto_pause = config.get_general('auto_pause')
    clipboard_thread = None
    websocket_server_thread = None
    screenshot_thread = None
    directory_watcher_thread = None
    unix_socket_server = None
    key_combo_listener = None
    auto_pause_handler = None
    engine_index = engine_keys.index(default_engine) if default_engine != '' else 0
    engine_index_2 = engine_keys.index(engine_secondary) if engine_secondary != '' else -1
    engine_color = config.get_general('engine_color')
    combo_pause = config.get_general('combo_pause')
    combo_engine_switch = config.get_general('combo_engine_switch')
    screen_capture_periodic = False
    screen_capture_on_combo = False
    coordinate_selector_event = threading.Event()
    notifier = DesktopNotifierSync()
    image_queue = queue.Queue()
    key_combos = {}

    if combo_pause != '':
        key_combos[combo_pause] = pause_handler
    if combo_engine_switch != '':
        key_combos[combo_engine_switch] = engine_change_handler

    if 'websocket' in (read_from, read_from_secondary) or write_to == 'websocket':
        websocket_port = config.get_general('websocket_port')
        logger.info(f"Starting websocket server on port {websocket_port}")
        websocket_server_thread = WebsocketServerThread('websocket' in (read_from, read_from_secondary))
        websocket_server_thread.start()
    if any(x in ('screencapture', 'obs') for x in (read_from, read_from_secondary)):
        global screenshot_request_queue
        screen_capture_delay_secs = config.get_general('screen_capture_delay_secs')
        screen_capture_combo = config.get_general('screen_capture_combo')
        coordinate_selector_combo = config.get_general('coordinate_selector_combo')
        last_screenshot_time = 0
        if screen_capture_combo != '':
            screen_capture_on_combo = True
            key_combos[screen_capture_combo] = on_screenshot_combo
        if coordinate_selector_combo != '':
            key_combos[coordinate_selector_combo] = on_coordinate_selector_combo
        if screen_capture_delay_secs != -1:
            global periodic_screenshot_queue
            periodic_screenshot_queue = queue.Queue()
            screen_capture_periodic = True
        if not (screen_capture_on_combo or screen_capture_periodic):
            exit_with_error('screen_capture_delay_secs or screen_capture_combo need to be valid values')
        screenshot_request_queue = queue.Queue()
        screenshot_thread = ScreenshotThread()
        screenshot_thread.start()
        read_from_readable.append('screen capture')
    if 'obs' in (read_from, read_from_secondary):
        last_screenshot_time = 0
        last_result = ([], engine_index)
        screenshot_event = threading.Event()
        obs_screenshot_thread = OBSScreenshotThread(
            gsm_ocr_config, screen_capture_on_combo, interval=screen_capture_delay_secs, is_manual_ocr=bool(screen_capture_on_combo))
        obs_screenshot_thread.start()
        filtering = TextFiltering()
        read_from_readable.append('obs')
    if 'websocket' in (read_from, read_from_secondary):
        read_from_readable.append('websocket')
    if 'unixsocket' in (read_from, read_from_secondary):
        if sys.platform == 'win32':
            exit_with_error('"unixsocket" is not currently supported on Windows')
        socket_path = Path('/tmp/owocr.sock')
        if socket_path.exists():
            try:
                test_socket = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                test_socket.connect(str(socket_path))
                test_socket.close()
                exit_with_error('Unix domain socket is already in use')
            except ConnectionRefusedError:
                socket_path.unlink()
        unix_socket_server = socketserver.ThreadingUnixStreamServer(str(socket_path), UnixSocketRequestHandler)
        unix_socket_server_thread = threading.Thread(target=unix_socket_server.serve_forever, daemon=True)
        unix_socket_server_thread.start()
        read_from_readable.append('unix socket')
    if 'clipboard' in (read_from, read_from_secondary):
        clipboard_thread = ClipboardThread()
        clipboard_thread.start()
        read_from_readable.append('clipboard')
    if any(i and i not in non_path_inputs for i in (read_from, read_from_secondary)):
        if all(i and i not in non_path_inputs for i in (read_from, read_from_secondary)):
            exit_with_error("read_from and read_from_secondary can't both be directory paths")
        delete_images = config.get_general('delete_images')
        read_from_path = Path(read_from) if read_from not in non_path_inputs else Path(
            read_from_secondary)
        if not read_from_path.is_dir():
            exit_with_error('read_from and read_from_secondary must be either "websocket", "unixsocket", "clipboard", "screencapture", or a path to a directory')
        directory_watcher_thread = DirectoryWatcher(read_from_path)
        directory_watcher_thread.start()
        read_from_readable.append(f'directory {read_from_path}')

    output_result = OutputResult()

    if len(key_combos) > 0:
        try:
            from pynput import keyboard
            key_combo_listener = keyboard.GlobalHotKeys(key_combos)
            key_combo_listener.start()
        except ImportError:
            pass

    if write_to in ('clipboard', 'websocket', 'callback'):
        write_to_readable = write_to
    else:
        if Path(write_to).suffix.lower() != '.txt':
            exit_with_error('write_to must be either "websocket", "clipboard" or a path to a text file')
        write_to_readable = f'file {write_to}'

    process_queue = (any(i in ('clipboard', 'websocket', 'unixsocket') for i in (read_from, read_from_secondary)) or read_from_path or screen_capture_on_combo)
    signal.signal(signal.SIGINT, terminate_handler)
    if auto_pause != 0:
        auto_pause_handler = AutopauseTimer()
    user_input_thread = threading.Thread(target=user_input_thread_run, daemon=True)
    user_input_thread.start()

    if not terminated.is_set():
        logger.opt(colors=True).info(f"Reading from {' and '.join(read_from_readable)}, writing to {write_to_readable} using <{engine_color}>{engine_instances[engine_index].readable_name}</>{' (paused)' if paused.is_set() else ''}")

    def handle_config_changes(changes):
        nonlocal last_result
        if any(c in changes for c in ('ocr1', 'ocr2', 'language', 'furigana_filter_sensitivity')):
            last_result = ([], engine_index)
            engine_change_handler_name(get_ocr_ocr1(), switch=True)
            engine_change_handler_name(get_ocr_ocr2(), switch=False)

    def handle_area_config_changes(changes):
        if screenshot_thread:
            screenshot_thread.ocr_config = get_scene_ocr_config()
        if obs_screenshot_thread:
            obs_screenshot_thread.init_config()
                
    config_check_thread.add_config_callback(handle_config_changes)
    config_check_thread.add_area_callback(handle_area_config_changes)
    previous_text = "Placeholder"
    sleep_time_to_add = 0
    last_result_time = time.time()
    while not terminated.is_set():
        ocr_start_time = datetime.now()
        start_time = time.time()
        img = None
        skip_waiting = False
        filter_text = False
        auto_pause = True
        notify = False

        if process_queue:
            try:
                img, is_screen_capture = image_queue.get_nowait()
                if not screen_capture_periodic and is_screen_capture:
                    filter_text = True
                if is_screen_capture:
                    auto_pause = False
                notify = True
            except queue.Empty:
                pass
            
        # if get_ocr_scan_rate() < .5:
        #     adjusted_scan_rate = min(get_ocr_scan_rate() + sleep_time_to_add, .5)
        # else:
        #     adjusted_scan_rate = get_ocr_scan_rate()
            
        # if (not img) and process_screenshots:
        #     if (not paused) and (not screenshot_thread or (screenshot_thread.screencapture_window_active and screenshot_thread.screencapture_window_visible)) and (time.time() - last_screenshot_time) > adjusted_scan_rate:
        #         screenshot_event.set()
        #         img = periodic_screenshot_queue.get()
        #         filter_img = True
        #         notify = False
        #         last_screenshot_time = time.time()
        #         ocr_start_time = datetime.now()
        #         if adjusted_scan_rate > get_ocr_scan_rate():
        #             ocr_start_time = ocr_start_time - timedelta(seconds=adjusted_scan_rate - get_ocr_scan_rate())

        # if img == 0:
        #     on_window_closed(False)
        #     terminated = True
        #     break
        # elif img:
        #     if filter_img:
        #         ocr_config = get_scene_ocr_config()
        #         # Check if the image is completely empty (all white or all black)
        #         try:
        #             extrema = img.getextrema()
        #             # For RGB or RGBA images, extrema is a tuple of (min, max) for each channel
        #             if isinstance(extrema[0], tuple):
        #                 is_empty = all(e[0] == e[1] for e in extrema)
        #             else:
        #                 is_empty = extrema[0] == extrema[1]
        #             if is_empty:
        #                 logger.info("Image is totally empty (all pixels the same), sleeping.")
        #                 sleep_time_to_add = .5
        #                 continue
        #         except Exception as e:
        #             logger.debug(f"Could not determine if image is empty: {e}")
                    
        #         # Compare images, but only if it's one box, multiple boxes skews results way too much and produces false positives
        #         # if ocr_config and len(ocr_config.rectangles) < 2:
        #         #     if are_images_similar(img, last_image):
        #         #         logger.info("Captured screenshot is similar to the last one, sleeping.")
        #         #         if time.time() - last_result_time > 10:
        #         #             sleep_time_to_add += .005
        #         #         continue
        #         # else:
        #         if are_images_identical(img, last_image, last_image_np):
        #             logger.info("Captured screenshot is identical to the last one, sleeping.")
        #             if time.time() - last_result_time > 10:
        #                 sleep_time_to_add += .005
        #             continue

        #         res, text = process_and_write_results(img, write_to, last_result, filtering, notify,
        #                                            ocr_start_time=ocr_start_time, furigana_filter_sensitivity=None if get_ocr_two_pass_ocr() else get_furigana_filter_sensitivity())
        #         if not text and not previous_text and time.time() - last_result_time > 10:
        #             sleep_time_to_add += .005
        #             logger.info(f"No text detected again, sleeping.")
        #         else:
        #             sleep_time_to_add = 0
                    
        #         # If image was stabilized, and now there is no text, reset sleep time
        #         if not previous_text and not res:
        #             sleep_time_to_add = 0
        #         previous_text = text
        #         if res:
        #             last_result = (res, engine_index)
        #             last_result_time = time.time()
        #     else:
        #         process_and_write_results(
        #             img, write_to, None, notify=notify, ocr_start_time=ocr_start_time, engine=ocr2)
        #     if isinstance(img, Path):
        #         if delete_images:
        #             Path.unlink(img)

        # if img == None and screen_capture_periodic:
            if (not paused.is_set()) and (time.time() - last_screenshot_time) > screen_capture_delay_secs:
                if periodic_screenshot_queue.empty() and screenshot_request_queue.empty():
                    screenshot_request_queue.put(False)
                try:
                    img = periodic_screenshot_queue.get(timeout=0.5)
                    filter_text = True
                    last_screenshot_time = time.time()
                except queue.Empty:
                    skip_waiting = True
                    pass

        if img:
            output_result(img, filter_text, auto_pause, notify)
            if isinstance(img, Path) and delete_images:
                Path.unlink(img)

        if not img and not skip_waiting:
            time.sleep(0.1)

    terminate_selector_if_running()
    user_input_thread.join()
    output_result.second_pass_thread.stop()
    if auto_pause_handler:
        auto_pause_handler.stop()
    if websocket_server_thread:
        websocket_server_thread.stop_server()
        websocket_server_thread.join()
    if clipboard_thread:
        if sys.platform == 'win32':
            win32api.PostThreadMessage(
                clipboard_thread.thread_id, win32con.WM_QUIT, 0, 0)
        clipboard_thread.join()
    if directory_watcher_thread:
        directory_watcher_thread.join()
    if unix_socket_server:
        unix_socket_server.shutdown()
        unix_socket_server.join()
    if screenshot_thread:
        screenshot_thread.join()
    if key_combo_listener:
        key_combo_listener.stop()
    if config_check_thread:
        config_check_thread.join()

def get_engine_names():
    global engine_instances
    return [instance.name for instance in engine_instances]
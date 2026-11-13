"""
Макро-автокликер: клики мыши, клавиши, сочетания, ввод текста, запись действий
(клавиатура, кнопки мыши, перемещения) с задержками, маскировка окна под фото
и «автоуход»: после цикла макроса программа открывает инвентарь, по снимку экрана
читает ЧИСЛА у шкал (распознавание цифр) и при низких значениях находит нужный предмет, наводит курсор и жмёт клавишу.

Запуск из Python:  python autoclicker_gui.py
Зависимости:       pip install pynput pillow numpy opencv-python-headless
"""

import base64
import ctypes
import io
import itertools
import json
import os
import random
import sys
import threading
import time
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

from pynput import keyboard, mouse
from PIL import Image, ImageGrab, ImageOps, ImageTk

try:
    import cv2
    import numpy as np
except ImportError:  # без них не работает только поиск предметов на экране
    cv2 = None
    np = None

# Чтобы координаты tkinter, pynput и снимков экрана совпадали при масштабировании Windows
if sys.platform == "win32":
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass

WINDOW_TITLE = "Главная - проводник"
IS_WIN = sys.platform == "win32"
Key = keyboard.Key
HOTKEYS = [f"F{i}" for i in range(1, 13)]
DATA_DIR = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), "AutoclickerMacro")
CONFIG_PATH = os.path.join(DATA_DIR, "config.json")

# (ключ, название, порог, действие, область ЧИСЛА справа от шкалы для экрана 1920x1080)
# Значения области подобраны по скриншоту инвентаря; на другом разрешении задайте область заново.
CARE_TARGETS = (
    ("food", "Верхняя шкала (еда)", 70, "e", (1112, 486, 1160, 504)),
    ("water", "Нижняя шкала (вода)", 5, "e", (1112, 513, 1160, 531)),
)
TARGET_LABEL = {t[0]: t[1] for t in CARE_TARGETS}

# ---------------------------------------------------------------- действия
ACTIONS = {
    "Клик мыши": "click",
    "Двойной клик": "double_click",
    "Переместить мышь": "move",
    "Зажать кнопку мыши": "mouse_down",
    "Отпустить кнопку мыши": "mouse_up",
    "Прокрутка колеса": "scroll",
    "Нажать клавишу": "key",
    "Зажать клавишу": "key_down",
    "Отпустить клавишу": "key_up",
    "Сочетание клавиш": "combo",
    "Ввести текст": "text",
}
ACTION_BY_TYPE = {v: k for k, v in ACTIONS.items()}

DEFAULT_ARGS = {
    "click": "left", "double_click": "left", "move": "500,300",
    "mouse_down": "left", "mouse_up": "left", "scroll": "0,-3",
    "key": "enter", "key_down": "shift", "key_up": "shift",
    "combo": "ctrl+c", "text": "Привет",
}
HINTS = {
    "click": "Кнопка: left / right / middle (или левая / правая / средняя). "
             "Можно с координатами: left 500,300",
    "double_click": "Так же, как клик: left или left 500,300",
    "move": "Координаты на экране: x,y  (например 500,300)",
    "mouse_down": "left / right / middle",
    "mouse_up": "left / right / middle",
    "scroll": "dx,dy или просто dy. Отрицательное — вниз: 0,-3",
    "key": "Одна клавиша: a, 5, enter, space, tab, esc, f5, up, backspace…",
    "key_down": "Клавиша, которая будет зажата: shift, ctrl, alt, a…",
    "key_up": "Клавиша, которую нужно отпустить",
    "combo": "Клавиши через плюс: ctrl+c, ctrl+shift+esc, alt+tab, win+d",
    "text": "Любой текст, он будет набран посимвольно",
}

BTN = {}
for _names, _btn in ((("left", "l", "левая", "лкм"), mouse.Button.left),
                     (("right", "r", "правая", "пкм"), mouse.Button.right),
                     (("middle", "m", "средняя", "скм"), mouse.Button.middle)):
    for _n in _names:
        BTN[_n] = _btn
BTN_NAME = {mouse.Button.left: "left", mouse.Button.right: "right",
            mouse.Button.middle: "middle"}

KEY_ALIASES = {
    "ctrl": Key.ctrl, "control": Key.ctrl, "shift": Key.shift, "alt": Key.alt,
    "win": Key.cmd, "cmd": Key.cmd, "super": Key.cmd,
    "enter": Key.enter, "return": Key.enter, "esc": Key.esc, "escape": Key.esc,
    "space": Key.space, "tab": Key.tab, "backspace": Key.backspace,
    "del": Key.delete, "delete": Key.delete,
    "pageup": Key.page_up, "pagedown": Key.page_down,
}
KEY_NORMALIZE = {
    "ctrl_l": "ctrl", "ctrl_r": "ctrl", "shift_l": "shift", "shift_r": "shift",
    "alt_l": "alt", "alt_r": "alt", "alt_gr": "alt",
    "cmd_l": "win", "cmd_r": "win", "cmd": "win",
}


def parse_button(token):
    try:
        return BTN[token.strip().lower()]
    except KeyError:
        raise ValueError(f"Неизвестная кнопка мыши: «{token}». Нужно left, right или middle.")


def parse_ints(text, count, what):
    parts = text.replace(",", " ").split()
    try:
        nums = [int(float(p)) for p in parts]
    except ValueError:
        raise ValueError(f"{what}: ожидаются числа, например 500,300")
    if len(nums) != count:
        raise ValueError(f"{what}: нужно {count} числа(ел), например 500,300")
    return nums


def parse_click(arg):
    parts = arg.replace(",", " ").split()
    if not parts:
        return mouse.Button.left, None
    btn = parse_button(parts[0])
    if len(parts) == 1:
        return btn, None
    if len(parts) == 3:
        try:
            return btn, (int(float(parts[1])), int(float(parts[2])))
        except ValueError:
            pass
    raise ValueError("Клик: left или left 500,300")


def parse_scroll(arg):
    parts = arg.replace(",", " ").split()
    try:
        nums = [int(float(p)) for p in parts]
    except ValueError:
        raise ValueError("Прокрутка: числа, например 0,-3")
    if len(nums) == 1:
        return 0, nums[0]
    if len(nums) == 2:
        return nums[0], nums[1]
    raise ValueError("Прокрутка: dx,dy или просто dy")


def parse_key(text):
    s = text.strip()
    low = s.lower()
    if not s:
        raise ValueError("Не указана клавиша")
    if low in KEY_ALIASES:
        return KEY_ALIASES[low]
    if len(s) > 2 and s[0] == "<" and s[-1] == ">" and s[1:-1].isdigit():
        return keyboard.KeyCode.from_vk(int(s[1:-1]))
    if len(s) == 1:
        if IS_WIN and low.isascii() and low.isalnum():
            return keyboard.KeyCode.from_vk(ord(low.upper()))
        return s
    member = getattr(Key, low, None)
    if isinstance(member, Key):
        return member
    raise ValueError(f"Неизвестная клавиша: «{s}»")


def key_to_str(key):
    """Клавиша из слушателя -> строка, которую понимает parse_key."""
    if isinstance(key, Key):
        return KEY_NORMALIZE.get(key.name, key.name)
    vk = getattr(key, "vk", None)
    if IS_WIN and vk is not None and (0x30 <= vk <= 0x39 or 0x41 <= vk <= 0x5A):
        return chr(vk).lower()
    char = getattr(key, "char", None)
    if char and char.isprintable() and char != " ":
        return char
    if vk is not None:
        return f"<{vk}>"
    return "?"


def check_step(s):
    """Проверяет шаг без выполнения. Бросает ValueError при ошибке."""
    t, a = s["type"], s["arg"].strip()
    if t in ("click", "double_click"):
        parse_click(a)
    elif t == "move":
        parse_ints(a, 2, "Перемещение")
    elif t in ("mouse_down", "mouse_up"):
        parse_button(a)
    elif t == "scroll":
        parse_scroll(a)
    elif t in ("key", "key_down", "key_up"):
        parse_key(a)
    elif t == "combo":
        keys = [k for k in a.split("+")]
        if not keys or not all(k.strip() for k in keys):
            raise ValueError("Сочетание: клавиши через плюс, например ctrl+c")
        for k in keys:
            parse_key(k)
    elif t == "text":
        if not a:
            raise ValueError("Введите текст")
    else:
        raise ValueError(f"Неизвестное действие: {t}")


def action_to_step(spec):
    """Короткая запись действия -> шаг. 'e' / 'ctrl+e' / 'mouse:right'."""
    s = spec.strip()
    if s.lower().startswith("mouse:"):
        return {"type": "click", "arg": s[6:].strip() or "left", "delay": 0}
    if "+" in s and len(s) > 1:
        return {"type": "combo", "arg": s, "delay": 0}
    return {"type": "key", "arg": s, "delay": 0}


# ------------------------------------------------- анализ изображения экрана
DIGITS_DIR = os.path.join(DATA_DIR, "digits")
MAX_PER_DIGIT = 6
# Стартовые цифры 0, 1, 2, 9 из скриншота инвентаря 1920x1080. Остальные программа
# запоминает кнопкой «Запомнить цифры» (шрифт игры и масштаб у каждого свой).
SEED_DIGITS = {'9': 'iVBORw0KGgoAAAANSUhEUgAAAAgAAAAKCAAAAACsrEBcAAAAZUlEQVR4nAFaAKX/AQ80RRn8pb4MAHvk//D/7o0KAOH/z3u1/95jAOzrYgoA0/90Av8UOwJRBPdLAK3//P/1///BBH3mTPfYDj7zABo2ARBb7P9mAIjv7Mn//7ZNAHna+f/upy8Ta7ow6TU2mL4AAAAASUVORK5CYII=', '2': 'iVBORw0KGgoAAAANSUhEUgAAAAgAAAAKCAAAAACsrEBcAAAAZUlEQVR4nAFaAKX/ARoGUzru8aLzAF7Z//r//8dTBDId3bYHTDhLABpoBxwOu/LgAAUWJAA75PvGABYWBEu8/NtTAA0kVtL/7G8RAByE//bnWhQRAJHy9P/3+eXYBA0NAPz6DgkBAmIn9QspQa4AAAAASUVORK5CYII=', '1': 'iVBORw0KGgoAAAANSUhEUgAAAAYAAAAKCAAAAACyZXDvAAAAUUlEQVR4nAFGALn/AQYbTjLJowAZlv//mxUEfkAAAP4UBGj77hL+LwSh6UMSCzMEaA5KAAACAvgAE/T28QIQBu//B94CAfHxDQKyAvMhAPwEAnTwGUyimb9sAAAAAElFTkSuQmCC', '0': 'iVBORw0KGgoAAAANSUhEUgAAAAgAAAAKCAAAAACsrEBcAAAAZUlEQVR4nAFaAKX/AQEtSzbptsn0AE7Z/////44FAMv/14qp/+VgBB/srJkvNSEvAg/sz+XK3wAzAgIOABL3CfoCAvQKA+7/DwHqBP8RO9cpEwHuAKv4+cP4/8I1ACKd/f/tymsAyBkr9XK6Bx4AAAAASUVORK5CYII='}


def need_cv():
    if cv2 is None or np is None:
        raise RuntimeError("Не установлены numpy и opencv-python-headless")


def _gray_to_array(img):
    return np.array(img.convert("L"), dtype=np.float32) / 255.0


def load_digit_templates():
    """Список (цифра, массив 0..1): стартовые + обученные пользователем."""
    need_cv()
    out = []
    for d, b64 in SEED_DIGITS.items():
        out.append((d, _gray_to_array(Image.open(io.BytesIO(base64.b64decode(b64))))))
    if os.path.isdir(DIGITS_DIR):
        for name in sorted(os.listdir(DIGITS_DIR)):
            if name.endswith(".png") and name[:1].isdigit():
                try:
                    out.append((name[0], _gray_to_array(Image.open(os.path.join(DIGITS_DIR, name)))))
                except Exception:  # noqa: BLE001
                    pass
    return out


def known_digits():
    try:
        return sorted({d for d, _ in load_digit_templates()})
    except Exception:  # noqa: BLE001
        return []


def save_digit(digit, arr):
    os.makedirs(DIGITS_DIR, exist_ok=True)
    path = os.path.join(DIGITS_DIR, f"{digit}_{int(time.time() * 1000)}.png")
    Image.fromarray((arr * 255).astype("uint8")).save(path)
    mine = sorted(n for n in os.listdir(DIGITS_DIR) if n.startswith(digit + "_"))
    for old in mine[:-MAX_PER_DIGIT]:
        try:
            os.remove(os.path.join(DIGITS_DIR, old))
        except OSError:
            pass


def _mask(img):
    g = np.array(img.convert("L"), dtype=np.float32)
    lo, hi = float(np.percentile(g, 5)), float(g.max())
    if hi - lo < 60:  # в области нет светлого текста
        return None, None
    return g, g > lo + 0.5 * (hi - lo)


def _bounds(mask):
    cols = mask.sum(axis=0)
    xs = np.where(cols >= 2)[0]
    if len(xs) == 0:
        return None
    return cols, int(xs.min()), int(xs.max()) + 1


def _split(cols, x1, x2, n, wmin, wmax):
    """Лучшее деление блока на n цифр по «впадинам» между ними (цифры могут касаться)."""
    if n == 1:
        return [x1, x2] if wmin <= x2 - x1 <= wmax else None
    best = None
    for cuts in itertools.combinations(range(x1 + wmin, x2 - wmin + 1), n - 1):
        b = [x1, *cuts, x2]
        w = [b[i + 1] - b[i] for i in range(n)]
        if any(not wmin <= v <= wmax for v in w):
            continue
        cost = float(sum(cols[c - 1] + cols[c] for c in cuts)) + 0.01 * (max(w) - min(w))
        if best is None or cost < best[0]:
            best = (cost, b)
    return best[1] if best else None


def _parts(g, mask, bounds):
    parts = []
    for a, b in zip(bounds[:-1], bounds[1:]):
        sub = mask[:, a:b]
        xs, ys = np.where(sub.any(axis=0))[0], np.where(sub.any(axis=1))[0]
        if len(xs) == 0 or len(ys) == 0:
            return None
        crop = g[ys.min():ys.max() + 1, a + xs.min():a + xs.max() + 1]
        parts.append((crop - crop.min()) / max(1e-6, float(crop.max() - crop.min())))
    return parts


def teach_parts(img, text):
    """Режет число на len(text) цифр. Возвращает [(цифра, массив)] или None."""
    need_cv()
    g, mask = _mask(img)
    if g is None:
        return None
    b = _bounds(mask)
    if b is None:
        return None
    cols, x1, x2 = b
    bounds = _split(cols, x1, x2, len(text), 3, 16)
    parts = _parts(g, mask, bounds) if bounds else None
    return list(zip(text, parts)) if parts else None


def _match_digit(cand, templates):
    scores = {}
    ch, cw = cand.shape
    for d, t in templates:
        th, tw = t.shape
        if abs(th - ch) > 2 or abs(tw - cw) > 2 or t.std() < 1e-3:
            continue
        H, W = max(th, ch) + 4, max(tw, cw) + 4
        canvas = np.zeros((H, W), np.float32)
        oy, ox = (H - ch) // 2, (W - cw) // 2
        canvas[oy:oy + ch, ox:ox + cw] = cand
        r = cv2.matchTemplate(canvas, t.astype(np.float32), cv2.TM_CCOEFF_NORMED)
        scores[d] = max(scores.get(d, -1.0), float(np.nan_to_num(r).max()))
    if not scores:
        return None, -1.0, 0.0
    ranked = sorted(scores.items(), key=lambda kv: -kv[1])
    gap = ranked[0][1] - ranked[1][1] if len(ranked) > 1 else 1.0
    return ranked[0][0], ranked[0][1], gap


def read_number(img, templates, min_score=0.7, min_gap=0.03):
    """Читает число (0..100) по цифрам. None, если цифры не распознаны."""
    need_cv()
    g, mask = _mask(img)
    if g is None or not templates:
        return None
    b = _bounds(mask)
    if b is None:
        return None
    cols, x1, x2 = b
    ws = [t.shape[1] for _, t in templates]
    wmin, wmax = max(3, min(ws) - 2), max(ws) + 2
    best = None
    for n in (1, 2, 3):
        bounds = _split(cols, x1, x2, n, wmin, wmax)
        parts = _parts(g, mask, bounds) if bounds else None
        if not parts:
            continue
        digits, score, ok = "", 1.0, True
        for c in parts:
            d, sc, gap = _match_digit(c, templates)
            if d is None or gap < min_gap:
                ok = False
                break
            digits += d
            score = min(score, sc)
        if ok and (best is None or score > best[0]):
            best = (score, digits)
    if best is None or best[0] < min_score:
        return None
    v = int(best[1])
    return v if 0 <= v <= 100 else None


def read_value(shot, region, templates):
    x1, y1, x2, y2 = region
    w, h = shot.size
    x1, x2, y1, y2 = max(0, x1), min(w, x2), max(0, y1), min(h, y2)
    if x2 - x1 < 10 or y2 - y1 < 6:
        raise ValueError("Область числа слишком мала или вне экрана")
    return read_number(shot.convert("RGB").crop((x1, y1, x2, y2)), templates)


def find_template(shot, paths, area=None):
    """Ищет лучшее совпадение среди шаблонов. Возвращает (оценка 0..1, x, y центра)."""
    if cv2 is None:
        raise RuntimeError("Не установлены numpy и opencv-python-headless")
    ox = oy = 0
    img = shot.convert("RGB")
    if area:
        ox, oy = area[0], area[1]
        img = img.crop(tuple(area))
    hay = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2BGR)
    best = (-1.0, 0, 0)
    for p in paths:
        try:
            tpl = cv2.imdecode(np.fromfile(p, dtype=np.uint8), cv2.IMREAD_COLOR)
        except Exception:
            tpl = None
        if tpl is None or tpl.shape[0] > hay.shape[0] or tpl.shape[1] > hay.shape[1]:
            continue
        if float(tpl.reshape(-1, 3).std(axis=0).max()) < 4:  # однотонный шаблон даёт ложные «идеальные» совпадения
            continue
        res = cv2.matchTemplate(hay, tpl, cv2.TM_CCOEFF_NORMED)
        res = np.nan_to_num(res, nan=0.0, posinf=0.0, neginf=0.0)
        _, score, _, loc = cv2.minMaxLoc(res)
        if score > best[0]:
            best = (float(score), ox + loc[0] + tpl.shape[1] // 2, oy + loc[1] + tpl.shape[0] // 2)
    return best


class RegionPicker:
    """Показывает снимок экрана на весь экран; область выделяется мышью. Esc — отмена."""

    def __init__(self, root, shot, on_done):
        self.on_done = on_done
        self.start = None
        self.rect = None
        w, h = shot.size
        self.top = tk.Toplevel(root)
        self.top.overrideredirect(True)
        self.top.geometry(f"{w}x{h}+0+0")
        self.top.attributes("-topmost", True)
        self.photo = ImageTk.PhotoImage(shot)
        self.canvas = tk.Canvas(self.top, width=w, height=h, highlightthickness=0, cursor="crosshair")
        self.canvas.pack()
        self.canvas.create_image(0, 0, image=self.photo, anchor="nw")
        self.canvas.create_text(w // 2, 28, fill="yellow", font=("TkDefaultFont", 16, "bold"),
                                text="Выделите область мышью (зажмите левую кнопку). Esc — отмена")
        self.canvas.bind("<ButtonPress-1>", self.press)
        self.canvas.bind("<B1-Motion>", self.drag)
        self.canvas.bind("<ButtonRelease-1>", self.release)
        for widget in (self.canvas, self.top):
            widget.bind("<Escape>", lambda e: self.finish(None))
            widget.bind("<Button-3>", lambda e: self.finish(None))
        self.top.focus_force()
        self.canvas.focus_set()

    def press(self, e):
        self.start = (e.x, e.y)
        self.rect = self.canvas.create_rectangle(e.x, e.y, e.x, e.y, outline="red", width=2)

    def drag(self, e):
        if self.rect:
            self.canvas.coords(self.rect, self.start[0], self.start[1], e.x, e.y)

    def release(self, e):
        if not self.start:
            return
        x1, x2 = sorted((self.start[0], e.x))
        y1, y2 = sorted((self.start[1], e.y))
        self.finish((x1, y1, x2 + 1, y2 + 1) if x2 - x1 >= 2 and y2 - y1 >= 0 else None)

    def finish(self, bbox):
        self.top.destroy()
        self.on_done(bbox)


# ---------------------------------------------------------------- программа
class App:
    def __init__(self, root):
        self.root = root
        root.title(WINDOW_TITLE)
        root.geometry("940x660")
        root.minsize(780, 580)

        self.mouse = mouse.Controller()
        self.kb = keyboard.Controller()

        self.steps = []
        self.playing = False
        self.recording = False
        self.stop_evt = threading.Event()
        self.rec_lock = threading.Lock()
        self.rec_events = []
        self.rec_last_t = None
        self.rec_last_pos = None
        self.rec_last_move_t = 0.0
        self.rec_down = set()
        self.mouse_listener = None
        self.win_rect = (0, 0, 0, 0)

        self.disguised = False
        self.disguise_src = None
        self.cover_photo = None
        self.photo_path = ""
        self.resize_job = None

        self.hk = {"play": "f6", "rec": "f7", "disguise": "f8"}
        self.hk_held = set()

        # автоуход
        self.care_win = None
        self.hidden = []
        self.care_log = tk.StringVar(value="")
        self.digits_text = tk.StringVar(value="")
        self.care_vars = {
            "enabled": tk.BooleanVar(value=False), "every": tk.StringVar(value="1"),
            "open_key": tk.StringVar(value="i"), "open_wait": tk.StringVar(value="700"),
            "close_key": tk.StringVar(value="i"),
        }
        self.tvars, self.tstate = {}, {}
        for key, _label, thr, action, region in CARE_TARGETS:
            self.tvars[key] = {
                "use": tk.BooleanVar(value=True), "thr": tk.StringVar(value=str(thr)),
                "action": tk.StringVar(value=action), "hover": tk.BooleanVar(value=True),
                "match": tk.StringVar(value="0.80"), "region_text": tk.StringVar(), "teach": tk.StringVar(),
                "tpl_text": tk.StringVar(), "search_text": tk.StringVar(),
            }
            self.tstate[key] = {"num_region": list(region), "search": None, "templates": []}
            self.update_target_labels(key)

        self.build_ui()
        self.load_config()
        self.update_digits_label()

        root.update_idletasks()
        self.update_rect()
        root.bind("<Configure>", self.on_configure)
        root.protocol("WM_DELETE_WINDOW", self.close)

        self.listener = keyboard.Listener(on_press=self.on_press, on_release=self.on_release)
        self.listener.daemon = True
        self.listener.start()

    # ------------------------------------------------------------ интерфейс
    def build_ui(self):
        self.main = ttk.Frame(self.root, padding=8)
        self.main.pack(fill="both", expand=True)
        self.cover = tk.Label(self.root, bd=0, bg="white")

        # --- настройки запуска
        run = ttk.LabelFrame(self.main, text="Запуск", padding=6)
        run.pack(fill="x")
        self.count_var = tk.StringVar(value="1")
        self.pause_var = tk.StringVar(value="0")
        self.speed_var = tk.StringVar(value="100")
        self.hold_var = tk.StringVar(value="50")
        self.jitter_var = tk.StringVar(value="0")
        fields = (("Повторов (0 = ∞):", self.count_var),
                  ("Пауза между повторами, мс:", self.pause_var),
                  ("Скорость, %:", self.speed_var),
                  ("Удержание клика, мс:", self.hold_var),
                  ("Разброс задержек, мс:", self.jitter_var))
        for i, (label, var) in enumerate(fields):
            ttk.Label(run, text=label).grid(row=0, column=i * 2, sticky="e", padx=(8, 2))
            ttk.Entry(run, textvariable=var, width=6).grid(row=0, column=i * 2 + 1)

        # --- горячие клавиши и маскировка
        hot = ttk.LabelFrame(self.main, text="Горячие клавиши и маскировка", padding=6)
        hot.pack(fill="x", pady=(6, 0))
        self.play_key = tk.StringVar(value="F6")
        self.rec_key = tk.StringVar(value="F7")
        self.disg_key = tk.StringVar(value="F8")
        for i, (label, var, name) in enumerate((
                ("Запуск/стоп:", self.play_key, "play"),
                ("Запись:", self.rec_key, "rec"),
                ("Маскировка:", self.disg_key, "disguise"))):
            ttk.Label(hot, text=label).grid(row=0, column=i * 2, sticky="e", padx=(8, 2))
            ttk.Combobox(hot, textvariable=var, values=HOTKEYS, width=5,
                         state="readonly").grid(row=0, column=i * 2 + 1)
            var.trace_add("write", lambda *_, n=name, v=var: self.hk.__setitem__(n, v.get().lower()))
        ttk.Button(hot, text="Выбрать фото…", command=self.choose_photo).grid(row=0, column=6, padx=(16, 4))
        self.photo_var = tk.StringVar(value="фото не выбрано")
        ttk.Label(hot, textvariable=self.photo_var, foreground="gray").grid(row=0, column=7, sticky="w")

        # --- список действий
        box = ttk.Frame(self.main)
        box.pack(fill="both", expand=True, pady=6)
        self.tree = ttk.Treeview(box, columns=("n", "act", "arg", "delay"),
                                 show="headings", height=12, selectmode="browse")
        for col, title, width, anchor in (("n", "№", 50, "center"), ("act", "Действие", 190, "w"),
                                          ("arg", "Параметр", 380, "w"), ("delay", "Задержка после, мс", 130, "center")):
            self.tree.heading(col, text=title)
            self.tree.column(col, width=width, anchor=anchor)
        sb = ttk.Scrollbar(box, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        self.tree.bind("<<TreeviewSelect>>", self.on_select)

        # --- форма шага
        form = ttk.LabelFrame(self.main, text="Шаг", padding=6)
        form.pack(fill="x")
        self.action_var = tk.StringVar(value="Клик мыши")
        self.arg_var = tk.StringVar(value=DEFAULT_ARGS["click"])
        self.fdelay_var = tk.StringVar(value="100")
        cb = ttk.Combobox(form, textvariable=self.action_var, values=list(ACTIONS), width=22, state="readonly")
        cb.grid(row=0, column=0, padx=4)
        cb.bind("<<ComboboxSelected>>", self.on_action_change)
        ttk.Entry(form, textvariable=self.arg_var, width=34).grid(row=0, column=1, padx=4)
        ttk.Label(form, text="Задержка после, мс:").grid(row=0, column=2, padx=(10, 2))
        ttk.Entry(form, textvariable=self.fdelay_var, width=7).grid(row=0, column=3)
        self.hint_var = tk.StringVar(value=HINTS["click"])
        ttk.Label(form, textvariable=self.hint_var, foreground="gray", wraplength=860).grid(
            row=1, column=0, columnspan=6, sticky="w", padx=4, pady=(4, 0))
        btns = ttk.Frame(form)
        btns.grid(row=2, column=0, columnspan=6, sticky="w", pady=(6, 0))
        for text, cmd in (("Добавить", self.add_step), ("Заменить выбранный", self.replace_step),
                          ("Удалить", self.delete_step), ("Вверх", lambda: self.move_step(-1)),
                          ("Вниз", lambda: self.move_step(1)), ("Очистить всё", self.clear_steps)):
            ttk.Button(btns, text=text, command=cmd).pack(side="left", padx=3)

        # --- нижняя панель
        bottom = ttk.Frame(self.main)
        bottom.pack(fill="x", pady=(8, 0))
        self.play_btn = ttk.Button(bottom, text="▶ Запустить", command=self.on_play_button)
        self.play_btn.pack(side="left", padx=3)
        self.rec_btn = ttk.Button(bottom, text="⏺ Записать", command=self.toggle_record)
        self.rec_btn.pack(side="left", padx=3)
        ttk.Button(bottom, text="Автоуход…", command=self.open_care).pack(side="left", padx=(20, 3))
        ttk.Button(bottom, text="Сохранить…", command=self.save_preset).pack(side="left", padx=(20, 3))
        ttk.Button(bottom, text="Загрузить…", command=self.load_preset).pack(side="left", padx=3)
        self.status_var = tk.StringVar(value="Готово")
        ttk.Label(bottom, textvariable=self.status_var, font=("TkDefaultFont", 10, "bold")).pack(side="right", padx=6)

    def notify(self, text, error=False):
        self.status_var.set(text)
        if error and not self.disguised:
            messagebox.showerror("Ошибка", text)

    # ------------------------------------------------------- список шагов
    def refresh_tree(self, select=None):
        self.tree.delete(*self.tree.get_children())
        for i, s in enumerate(self.steps):
            self.tree.insert("", "end", iid=str(i),
                             values=(i + 1, ACTION_BY_TYPE.get(s["type"], s["type"]), s["arg"], s["delay"]))
        if select is not None and 0 <= select < len(self.steps):
            self.tree.selection_set(str(select))
            self.tree.see(str(select))

    def selected_index(self):
        sel = self.tree.selection()
        return int(sel[0]) if sel else None

    def on_select(self, _event=None):
        i = self.selected_index()
        if i is None:
            return
        s = self.steps[i]
        self.action_var.set(ACTION_BY_TYPE.get(s["type"], "Клик мыши"))
        self.arg_var.set(s["arg"])
        self.fdelay_var.set(str(s["delay"]))
        self.hint_var.set(HINTS.get(s["type"], ""))

    def on_action_change(self, _event=None):
        t = ACTIONS[self.action_var.get()]
        self.arg_var.set(DEFAULT_ARGS[t])
        self.hint_var.set(HINTS[t])

    def form_step(self):
        t = ACTIONS[self.action_var.get()]
        try:
            delay = int(float(self.fdelay_var.get().replace(",", ".")))
            if delay < 0:
                raise ValueError
        except ValueError:
            self.notify("Задержка должна быть числом ≥ 0", error=True)
            return None
        s = {"type": t, "arg": self.arg_var.get().strip(), "delay": delay}
        try:
            check_step(s)
        except ValueError as e:
            self.notify(str(e), error=True)
            return None
        return s

    def add_step(self):
        s = self.form_step()
        if s is None:
            return
        i = self.selected_index()
        pos = i + 1 if i is not None else len(self.steps)
        self.steps.insert(pos, s)
        self.refresh_tree(pos)

    def replace_step(self):
        i = self.selected_index()
        if i is None:
            self.notify("Сначала выберите шаг в списке", error=True)
            return
        s = self.form_step()
        if s is None:
            return
        self.steps[i] = s
        self.refresh_tree(i)

    def delete_step(self):
        i = self.selected_index()
        if i is None:
            return
        del self.steps[i]
        self.refresh_tree(min(i, len(self.steps) - 1))

    def move_step(self, d):
        i = self.selected_index()
        if i is None or not 0 <= i + d < len(self.steps):
            return
        self.steps[i], self.steps[i + d] = self.steps[i + d], self.steps[i]
        self.refresh_tree(i + d)

    def clear_steps(self):
        if self.steps and messagebox.askyesno("Очистить", "Удалить все шаги из списка?"):
            self.steps = []
            self.refresh_tree()

    # ---------------------------------------------------------- выполнение
    def num(self, var):
        return float(var.get().replace(",", "."))

    def read_settings(self):
        try:
            cfg = {"count": int(self.num(self.count_var)), "pause": self.num(self.pause_var),
                   "speed": self.num(self.speed_var), "hold": self.num(self.hold_var),
                   "jitter": self.num(self.jitter_var)}
        except ValueError:
            raise ValueError("Настройки запуска должны быть числами")
        if cfg["count"] < 0 or cfg["pause"] < 0 or cfg["speed"] <= 0 or cfg["hold"] < 0 or cfg["jitter"] < 0:
            raise ValueError("Скорость должна быть > 0, остальные значения ≥ 0")
        return cfg

    def on_play_button(self):
        if self.playing:
            self.stop_evt.set()
        elif not self.recording:
            self.status_var.set("Старт через 2 с — наведите курсор…")
            self.root.after(2000, self.start_play)

    def toggle_play(self):
        if self.playing:
            self.stop_evt.set()
        else:
            self.start_play()

    def start_play(self):
        if self.playing or self.recording:
            return
        if not self.steps:
            self.notify("Список действий пуст", error=True)
            return
        try:
            cfg = self.read_settings()
            care = self.read_care()
        except ValueError as e:
            self.notify(str(e), error=True)
            return
        self.playing = True
        self.stop_evt = threading.Event()
        self.play_btn.config(text="■ Остановить")
        self.status_var.set("Выполняется…")
        threading.Thread(target=self.play_loop, args=(list(self.steps), cfg, care, self.stop_evt),
                         daemon=True).start()

    def play_loop(self, steps, cfg, care, stop):
        hold = cfg["hold"] / 1000
        cycle = 0
        try:
            while not stop.is_set():
                for s in steps:
                    if stop.is_set():
                        break
                    self.exec_step(s, hold)
                    d = s["delay"] * 100 / cfg["speed"] + random.uniform(0, cfg["jitter"])
                    if stop.wait(max(d, 1) / 1000):
                        break
                if stop.is_set():
                    break
                cycle += 1
                if cfg["count"] and cycle >= cfg["count"]:
                    break
                if care["enabled"] and cycle % care["every"] == 0:
                    self.run_care(care, hold, stop)
                    if stop.is_set():
                        break
                if cfg["pause"] and stop.wait(cfg["pause"] / 1000):
                    break
                if stop.wait(0.001):
                    break
        except Exception as e:  # noqa: BLE001
            msg = f"Ошибка выполнения: {e}"
            self.root.after(0, lambda: self.notify(msg, error=True))
        finally:
            self.root.after(0, self.on_play_finished)

    def on_play_finished(self):
        self.playing = False
        self.play_btn.config(text="▶ Запустить")
        if self.status_var.get() == "Выполняется…":
            self.status_var.set("Остановлено")

    def exec_step(self, s, hold):
        t, a = s["type"], s["arg"].strip()
        m, k = self.mouse, self.kb
        if t in ("click", "double_click"):
            btn, xy = parse_click(a)
            if xy:
                m.position = xy
                time.sleep(0.01)
            for i in range(2 if t == "double_click" else 1):
                m.press(btn)
                time.sleep(hold)
                m.release(btn)
                if i == 0 and t == "double_click":
                    time.sleep(0.05)
        elif t == "move":
            x, y = parse_ints(a, 2, "Перемещение")
            m.position = (x, y)
        elif t == "mouse_down":
            m.press(parse_button(a))
        elif t == "mouse_up":
            m.release(parse_button(a))
        elif t == "scroll":
            dx, dy = parse_scroll(a)
            m.scroll(dx, dy)
        elif t == "key":
            key = parse_key(a)
            k.press(key)
            time.sleep(hold)
            k.release(key)
        elif t == "key_down":
            k.press(parse_key(a))
        elif t == "key_up":
            k.release(parse_key(a))
        elif t == "combo":
            keys = [parse_key(p) for p in a.split("+")]
            for key in keys:
                k.press(key)
                time.sleep(0.02)
            time.sleep(hold)
            for key in reversed(keys):
                k.release(key)
                time.sleep(0.02)
        elif t == "text":
            k.type(a)

    # ------------------------------------------------------------ автоуход
    def update_target_labels(self, key):
        s, v = self.tstate[key], self.tvars[key]
        r = s["num_region"]
        v["region_text"].set(f"Область числа: {r[0]},{r[1]} — {r[2]},{r[3]}" if r else "Область числа: не задана")
        v["tpl_text"].set(f"Шаблонов предмета: {len(s['templates'])}")
        a = s["search"]
        v["search_text"].set(f"Область поиска: {a[0]},{a[1]} — {a[2]},{a[3]}" if a else "Область поиска: весь экран")

    def update_digits_label(self):
        known = known_digits()
        missing = [str(d) for d in range(10) if str(d) not in known]
        text = "Известные цифры: " + (" ".join(known) if known else "нет")
        if missing:
            text += "   |   Ещё не знаю: " + " ".join(missing)
        else:
            text += "   |   знаю все цифры"
        self.digits_text.set(text)

    def read_care(self, force=False):
        cv = self.care_vars
        if not (cv["enabled"].get() or force):
            return {"enabled": False}
        try:
            care = {"enabled": True, "every": int(self.num(cv["every"])),
                    "open_key": cv["open_key"].get().strip(), "close_key": cv["close_key"].get().strip(),
                    "open_wait": self.num(cv["open_wait"]), "targets": {}}
        except ValueError:
            raise ValueError("Автоуход: «каждые N циклов» и пауза должны быть числами")
        if care["every"] < 1 or care["open_wait"] < 0:
            raise ValueError("Автоуход: «каждые N циклов» ≥ 1, пауза ≥ 0")
        for what, spec in (("открытия инвентаря", care["open_key"]), ("закрытия инвентаря", care["close_key"])):
            try:
                check_step(action_to_step(spec))
            except ValueError as e:
                raise ValueError(f"Автоуход, клавиша {what}: {e}")
        for key, label, *_ in CARE_TARGETS:
            v, s = self.tvars[key], self.tstate[key]
            try:
                t = {"use": v["use"].get(), "thr": self.num(v["thr"]), "match": self.num(v["match"]),
                     "action": v["action"].get().strip(), "hover": v["hover"].get(),
                     "num_region": list(s["num_region"]), "search": list(s["search"]) if s["search"] else None,
                     "templates": list(s["templates"])}
            except ValueError:
                raise ValueError(f"Автоуход, {label}: порог и совпадение должны быть числами")
            if t["use"]:
                if not 0.3 <= t["match"] <= 1:
                    raise ValueError(f"Автоуход, {label}: совпадение должно быть от 0.3 до 1")
                try:
                    check_step(action_to_step(t["action"]))
                except ValueError as e:
                    raise ValueError(f"Автоуход, {label}, действие: {e}")
                if not t["templates"]:
                    raise ValueError(f"Автоуход, {label}: добавьте хотя бы один шаблон предмета")
                if not t["num_region"]:
                    raise ValueError(f"Автоуход, {label}: задайте область числа")
            care["targets"][key] = t
        return care

    def run_care(self, care, hold, stop):
        """Открыть инвентарь -> снимок -> шкалы -> нужные предметы -> закрыть инвентарь."""
        log = []
        opened = False
        try:
            self.exec_step(action_to_step(care["open_key"]), hold)
            opened = True
            if stop.wait(care["open_wait"] / 1000):
                return
            shot = ImageGrab.grab()
            tpls = load_digit_templates()
            values = {}
            for key in ("food", "water"):
                t = care["targets"][key]
                if t["use"]:
                    values[key] = read_value(shot, t["num_region"], tpls)
            log.append(", ".join(f"{TARGET_LABEL[k]}: {v if v is not None else '?'}" for k, v in values.items()))
            first = True
            for key in ("water", "food"):  # сначала нижняя шкала, потом верхняя
                t = care["targets"][key]
                if key not in values:
                    continue
                val = values[key]
                if val is None:
                    log.append(f"{TARGET_LABEL[key]}: число не распознано, обучите цифры")
                    continue
                if val >= t["thr"]:
                    continue
                if not first:
                    if stop.wait(0.4):
                        return
                    shot = ImageGrab.grab()
                first = False
                score, x, y = find_template(shot, t["templates"], t["search"])
                if score < t["match"]:
                    log.append(f"{TARGET_LABEL[key]}: предмет не найден (совпадение {score:.2f})")
                    continue
                if t["hover"]:
                    self.mouse.position = (x, y)
                    if stop.wait(0.2):
                        return
                self.exec_step(action_to_step(t["action"]), hold)
                log.append(f"{TARGET_LABEL[key]}: предмет использован (совпадение {score:.2f})")
            if stop.wait(0.3):
                return
        finally:
            if opened:
                try:
                    self.exec_step(action_to_step(care["close_key"]), hold)
                except Exception:  # noqa: BLE001
                    pass
            msg = "Автоуход: " + "; ".join(x for x in log if x) if log else "Автоуход прерван"
            self.root.after(0, lambda: self.care_log.set(msg))

    # --- работа со снимками экрана в окне настроек
    def hide_windows(self):
        self.hidden = [self.root]
        self.root.withdraw()
        try:
            if self.care_win is not None and self.care_win.winfo_exists():
                self.care_win.withdraw()
                self.hidden.append(self.care_win)
        except tk.TclError:
            pass

    def show_windows(self):
        for w in self.hidden:
            try:
                w.deiconify()
            except tk.TclError:
                pass
        self.hidden = []

    def with_snapshot(self, callback):
        """3 секунды на переключение в игру, затем окна прячутся и делается снимок."""
        if self.playing or self.recording:
            self.notify("Сначала остановите запуск или запись", error=True)
            return
        self.care_log.set("Снимок экрана через 3 с — переключитесь на игру с открытым инвентарём…")

        def take():
            try:
                shot = ImageGrab.grab()
            except Exception as e:  # noqa: BLE001
                self.show_windows()
                self.notify(f"Не удалось сделать снимок экрана: {e}", error=True)
                return
            callback(shot)

        def hide():
            self.hide_windows()
            self.root.after(400, take)

        self.root.after(3000, hide)

    def pick_number(self, key):
        def on_shot(shot):
            def done(bbox):
                self.show_windows()
                if bbox:
                    self.tstate[key]["num_region"] = list(bbox)
                    self.update_target_labels(key)
                    self.care_log.set("Область числа задана. Нажмите «Прочитать число».")
            RegionPicker(self.root, shot, done)
        self.with_snapshot(on_shot)

    def check_number(self, key):
        def on_shot(shot):
            self.show_windows()
            try:
                val = read_value(shot, self.tstate[key]["num_region"], load_digit_templates())
                if val is None:
                    msg = (f"{TARGET_LABEL[key]}: число не распознано. Введите число, которое сейчас "
                           f"на экране, и нажмите «Запомнить цифры».")
                else:
                    msg = f"{TARGET_LABEL[key]}: {val}"
            except Exception as e:  # noqa: BLE001
                msg = f"Ошибка: {e}"
            self.care_log.set(msg)
        self.with_snapshot(on_shot)

    def teach_digits(self, key):
        text = "".join(ch for ch in self.tvars[key]["teach"].get() if ch.isdigit())
        if not text or len(text) > 3:
            self.notify("Введите число, которое сейчас показано у шкалы (1–3 цифры)", error=True)
            return

        def on_shot(shot):
            self.show_windows()
            x1, y1, x2, y2 = self.tstate[key]["num_region"]
            try:
                parts = teach_parts(shot.convert("RGB").crop((x1, y1, x2, y2)), text)
            except Exception as e:  # noqa: BLE001
                self.care_log.set(f"Ошибка: {e}")
                return
            if not parts:
                self.care_log.set(f"Не удалось выделить {len(text)} цифр(ы) в области числа. "
                                  f"Проверьте область и что в игре сейчас показано «{text}».")
                return
            for digit, arr in parts:
                save_digit(digit, arr)
            self.update_digits_label()
            self.care_log.set(f"Запомнены цифры: {' '.join(d for d, _ in parts)}")
        self.with_snapshot(on_shot)

    def add_template(self, key):
        def on_shot(shot):
            def done(bbox):
                self.show_windows()
                if not bbox:
                    return
                os.makedirs(DATA_DIR, exist_ok=True)
                path = os.path.join(DATA_DIR, f"{key}_{int(time.time() * 1000)}.png")
                shot.convert("RGB").crop(bbox).save(path)
                self.tstate[key]["templates"].append(path)
                self.update_target_labels(key)
                self.care_log.set("Шаблон добавлен.")
            RegionPicker(self.root, shot, done)
        self.with_snapshot(on_shot)

    def add_template_file(self, key):
        path = filedialog.askopenfilename(
            filetypes=[("Изображения", "*.png *.jpg *.jpeg *.bmp"), ("Все файлы", "*.*")])
        if path:
            self.tstate[key]["templates"].append(path)
            self.update_target_labels(key)

    def clear_templates(self, key):
        self.tstate[key]["templates"] = []
        self.update_target_labels(key)

    def pick_search(self, key):
        def on_shot(shot):
            def done(bbox):
                self.show_windows()
                if bbox:
                    self.tstate[key]["search"] = list(bbox)
                    self.update_target_labels(key)
            RegionPicker(self.root, shot, done)
        self.with_snapshot(on_shot)

    def reset_search(self, key):
        self.tstate[key]["search"] = None
        self.update_target_labels(key)

    def test_care(self):
        if self.playing or self.recording:
            return
        try:
            cfg = self.read_settings()
            care = self.read_care(force=True)
        except ValueError as e:
            self.notify(str(e), error=True)
            return
        self.care_log.set("Тест через 3 с — переключитесь на игру…")

        def finish():
            self.playing = False
            self.show_windows()

        def work(stop):
            try:
                self.run_care(care, cfg["hold"] / 1000, stop)
            except Exception as e:  # noqa: BLE001
                msg = f"Ошибка автоухода: {e}"
                self.root.after(0, lambda: self.care_log.set(msg))
            finally:
                self.root.after(0, finish)

        def go():
            self.hide_windows()
            self.playing = True
            self.stop_evt = threading.Event()
            stop = self.stop_evt
            self.root.after(400, lambda: threading.Thread(target=work, args=(stop,), daemon=True).start())

        self.root.after(3000, go)

    def open_care(self):
        if self.care_win is not None and self.care_win.winfo_exists():
            self.care_win.deiconify()
            self.care_win.lift()
            return
        w = tk.Toplevel(self.root)
        w.title("Автоуход")
        w.resizable(False, False)
        self.care_win = w
        f = ttk.Frame(w, padding=10)
        f.pack(fill="both", expand=True)
        cv = self.care_vars

        gen = ttk.LabelFrame(f, text="Общее", padding=6)
        gen.pack(fill="x")
        ttk.Checkbutton(gen, text="Включить автоуход после цикла макроса",
                        variable=cv["enabled"]).grid(row=0, column=0, columnspan=4, sticky="w")
        for i, (label, name, width) in enumerate((
                ("Каждые N циклов:", "every", 6), ("Пауза после открытия, мс:", "open_wait", 6),
                ("Клавиша открытия инвентаря:", "open_key", 8), ("Клавиша закрытия:", "close_key", 8))):
            r, c = 1 + i // 2, (i % 2) * 2
            ttk.Label(gen, text=label).grid(row=r, column=c, sticky="e", padx=(8, 2), pady=2)
            ttk.Entry(gen, textvariable=cv[name], width=width).grid(row=r, column=c + 1, sticky="w")

        for key, label, *_ in CARE_TARGETS:
            v = self.tvars[key]
            box = ttk.LabelFrame(f, text=label, padding=6)
            box.pack(fill="x", pady=(8, 0))
            ttk.Checkbutton(box, text="Использовать", variable=v["use"]).grid(row=0, column=0, sticky="w")
            ttk.Label(box, text="Порог, %: действовать, если меньше").grid(row=0, column=1, sticky="e", padx=(12, 2))
            ttk.Entry(box, textvariable=v["thr"], width=6).grid(row=0, column=2, sticky="w")
            ttk.Label(box, textvariable=v["region_text"]).grid(row=1, column=0, columnspan=2, sticky="w", pady=2)
            ttk.Button(box, text="Задать область числа", command=lambda k=key: self.pick_number(k)).grid(row=1, column=2, padx=3)
            ttk.Button(box, text="Прочитать число", command=lambda k=key: self.check_number(k)).grid(row=1, column=3, padx=3)
            teach = ttk.Frame(box)
            teach.grid(row=2, column=0, columnspan=5, sticky="w", pady=2)
            ttk.Label(teach, text="Число на экране сейчас:").pack(side="left")
            ttk.Entry(teach, textvariable=v["teach"], width=6).pack(side="left", padx=(4, 6))
            ttk.Button(teach, text="Запомнить цифры", command=lambda k=key: self.teach_digits(k)).pack(side="left")
            ttk.Label(box, textvariable=v["tpl_text"]).grid(row=3, column=0, columnspan=2, sticky="w", pady=2)
            ttk.Button(box, text="Шаблон с экрана", command=lambda k=key: self.add_template(k)).grid(row=3, column=2, padx=3)
            ttk.Button(box, text="Из файла…", command=lambda k=key: self.add_template_file(k)).grid(row=3, column=3, padx=3)
            ttk.Button(box, text="Очистить", command=lambda k=key: self.clear_templates(k)).grid(row=3, column=4, padx=3)
            ttk.Label(box, textvariable=v["search_text"]).grid(row=4, column=0, columnspan=2, sticky="w", pady=2)
            ttk.Button(box, text="Область поиска", command=lambda k=key: self.pick_search(k)).grid(row=4, column=2, padx=3)
            ttk.Button(box, text="Весь экран", command=lambda k=key: self.reset_search(k)).grid(row=4, column=3, padx=3)
            opt = ttk.Frame(box)
            opt.grid(row=5, column=0, columnspan=5, sticky="w", pady=(4, 0))
            ttk.Label(opt, text="Действие:").pack(side="left")
            ttk.Entry(opt, textvariable=v["action"], width=12).pack(side="left", padx=(2, 12))
            ttk.Label(opt, text="Совпадение (0.3–1):").pack(side="left")
            ttk.Entry(opt, textvariable=v["match"], width=6).pack(side="left", padx=(2, 12))
            ttk.Checkbutton(opt, text="Наводить курсор на предмет", variable=v["hover"]).pack(side="left")

        ttk.Label(f, textvariable=self.digits_text, wraplength=640).pack(anchor="w", pady=(8, 0))
        ttk.Label(f, foreground="gray", wraplength=640, text=(
            "Шкалы читаются по цифрам. Цифры 0, 1, 2 и 9 уже известны для экрана 1920×1080, остальные "
            "запоминаются кнопкой «Запомнить цифры»: когда у шкалы показано, например, 37, впишите 37 "
            "и нажмите кнопку (инвентарь должен быть открыт). Действие: клавиша (e, 1, enter), сочетание (ctrl+e) или клик мыши (mouse:right, mouse:left). "
            "Шаблон делайте по самой иконке предмета, без цифр количества и процентов. "
            "Во время работы окно программы не должно перекрывать игру, игра — в оконном или "
            "безрамочном режиме.")).pack(anchor="w", pady=(8, 0))
        ttk.Label(f, textvariable=self.care_log, font=("TkDefaultFont", 10, "bold"),
                  wraplength=640).pack(anchor="w", pady=(6, 0))
        row = ttk.Frame(f)
        row.pack(fill="x", pady=(8, 0))
        ttk.Button(row, text="Тест сейчас (через 3 с)", command=self.test_care).pack(side="left")
        ttk.Button(row, text="Закрыть", command=w.destroy).pack(side="right")

    # --------------------------------------------------------------- запись
    def toggle_record(self):
        if self.recording:
            self.stop_record()
        elif not self.playing:
            self.start_record()

    def start_record(self):
        with self.rec_lock:
            self.rec_events = []
            self.rec_last_t = None
            self.rec_last_pos = None
            self.rec_last_move_t = 0.0
            self.rec_down = set()
        self.recording = True
        self.rec_btn.config(text="■ Остановить запись")
        pos = self.mouse.position
        if not self.inside_own(*pos):
            self.rec_move(*pos)
        self.mouse_listener = mouse.Listener(on_move=self.on_mouse_move, on_click=self.on_mouse_click,
                                             on_scroll=self.on_mouse_scroll)
        self.mouse_listener.daemon = True
        self.mouse_listener.start()
        self.tick_rec()

    def tick_rec(self):
        if self.recording:
            self.status_var.set(f"Запись… событий: {len(self.rec_events)} "
                                f"(стоп: {self.rec_key.get()})")
            self.root.after(300, self.tick_rec)

    def stop_record(self):
        self.recording = False
        if self.mouse_listener:
            self.mouse_listener.stop()
            self.mouse_listener = None
        with self.rec_lock:
            events, self.rec_events = self.rec_events, []
        self.steps.extend(events)
        self.refresh_tree(len(self.steps) - 1 if events else None)
        self.rec_btn.config(text="⏺ Записать")
        self.status_var.set(f"Записано действий: {len(events)} (добавлены в конец списка)")

    def rec_add(self, typ, arg):
        with self.rec_lock:
            now = time.perf_counter()
            if self.rec_events and self.rec_last_t is not None:
                self.rec_events[-1]["delay"] = int((now - self.rec_last_t) * 1000)
            self.rec_last_t = now
            self.rec_events.append({"type": typ, "arg": arg, "delay": 0})

    def rec_move(self, x, y):
        self.rec_last_pos = (x, y)
        self.rec_last_move_t = time.perf_counter()
        self.rec_add("move", f"{x},{y}")

    def inside_own(self, x, y):
        rx, ry, w, h = self.win_rect
        return rx <= x < rx + w and ry - 40 <= y < ry + h

    def on_mouse_move(self, x, y):
        if not self.recording or self.inside_own(x, y):
            return
        if (x, y) == self.rec_last_pos or time.perf_counter() - self.rec_last_move_t < 0.02:
            return
        self.rec_move(x, y)

    def on_mouse_click(self, x, y, button, pressed):
        if not self.recording or self.inside_own(x, y):
            return
        if (x, y) != self.rec_last_pos:
            self.rec_move(x, y)
        self.rec_add("mouse_down" if pressed else "mouse_up", BTN_NAME.get(button, "left"))

    def on_mouse_scroll(self, x, y, dx, dy):
        if not self.recording or self.inside_own(x, y):
            return
        if (x, y) != self.rec_last_pos:
            self.rec_move(x, y)
        self.rec_add("scroll", f"{dx},{dy}")

    # ----------------------------------------------------------- клавиатура
    def on_press(self, key):
        name = key.name if isinstance(key, Key) else None
        if name:
            for action, hk in self.hk.items():
                if name == hk:
                    if name not in self.hk_held:
                        self.hk_held.add(name)
                        fn = {"play": self.toggle_play, "rec": self.toggle_record,
                              "disguise": self.toggle_disguise}[action]
                        self.root.after(0, fn)
                    return
        if self.recording:
            ks = key_to_str(key)
            if ks not in self.rec_down:
                self.rec_down.add(ks)
                self.rec_add("key_down", ks)

    def on_release(self, key):
        name = key.name if isinstance(key, Key) else None
        if name and name in self.hk.values():
            self.hk_held.discard(name)
            return
        if self.recording:
            ks = key_to_str(key)
            if ks in self.rec_down:
                self.rec_down.discard(ks)
                self.rec_add("key_up", ks)

    # ------------------------------------------------------------ маскировка
    def choose_photo(self):
        path = filedialog.askopenfilename(
            title="Фото для маскировки",
            filetypes=[("Изображения", "*.png *.jpg *.jpeg *.bmp *.gif *.webp"), ("Все файлы", "*.*")])
        if path:
            self.load_photo(path)

    def load_photo(self, path):
        try:
            img = Image.open(path).convert("RGB")
        except Exception as e:  # noqa: BLE001
            self.notify(f"Не удалось открыть фото: {e}", error=True)
            return
        self.disguise_src = img
        self.photo_path = path
        self.photo_var.set(os.path.basename(path))
        if self.disguised:
            self.render_cover()

    def toggle_disguise(self):
        if self.disguised:
            self.cover.pack_forget()
            self.main.pack(fill="both", expand=True)
            self.disguised = False
            return
        if self.disguise_src is None:
            self.notify("Сначала выберите фото для маскировки", error=True)
            return
        self.main.pack_forget()
        self.cover.pack(fill="both", expand=True)
        self.disguised = True
        self.root.update_idletasks()
        self.render_cover()

    def render_cover(self):
        w, h = self.root.winfo_width(), self.root.winfo_height()
        if w < 2 or h < 2 or self.disguise_src is None:
            return
        img = ImageOps.fit(self.disguise_src, (w, h), Image.LANCZOS)
        self.cover_photo = ImageTk.PhotoImage(img)
        self.cover.config(image=self.cover_photo)

    def update_rect(self):
        self.win_rect = (self.root.winfo_rootx(), self.root.winfo_rooty(),
                         self.root.winfo_width(), self.root.winfo_height())

    def on_configure(self, event):
        if event.widget is not self.root:
            return
        self.update_rect()
        if self.disguised:
            if self.resize_job:
                self.root.after_cancel(self.resize_job)
            self.resize_job = self.root.after(80, self.render_cover)

    # ------------------------------------------------- сохранение настроек
    def collect_care(self):
        cv = self.care_vars
        data = {"enabled": cv["enabled"].get(), "every": cv["every"].get(), "open_key": cv["open_key"].get(),
                "open_wait": cv["open_wait"].get(), "close_key": cv["close_key"].get(), "targets": {}}
        for key in self.tvars:
            v, s = self.tvars[key], self.tstate[key]
            data["targets"][key] = {
                "use": v["use"].get(), "thr": v["thr"].get(), "action": v["action"].get(),
                "hover": v["hover"].get(), "match": v["match"].get(), "num_region": s["num_region"],
                "search": s["search"], "templates": s["templates"]}
        return data

    def collect_data(self):
        return {
            "steps": self.steps,
            "settings": {
                "count": self.count_var.get(), "pause": self.pause_var.get(),
                "speed": self.speed_var.get(), "hold": self.hold_var.get(),
                "jitter": self.jitter_var.get(), "play_key": self.play_key.get(),
                "rec_key": self.rec_key.get(), "disguise_key": self.disg_key.get(),
                "photo": self.photo_path,
            },
            "care": self.collect_care(),
        }

    def apply_care(self, data):
        cv = self.care_vars
        for k in ("enabled", "every", "open_key", "open_wait", "close_key"):
            if k in data:
                cv[k].set(data[k])
        for key, t in data.get("targets", {}).items():
            if key not in self.tvars:
                continue
            v, s = self.tvars[key], self.tstate[key]
            for k in ("use", "thr", "action", "hover", "match"):
                if k in t:
                    v[k].set(t[k])
            if isinstance(t.get("num_region"), list) and len(t["num_region"]) == 4:
                s["num_region"] = [int(x) for x in t["num_region"]]
            srch = t.get("search")
            s["search"] = [int(x) for x in srch] if isinstance(srch, list) and len(srch) == 4 else None
            s["templates"] = [p for p in t.get("templates", []) if os.path.exists(p)]
            self.update_target_labels(key)

    def apply_data(self, data):
        steps = []
        for s in data["steps"]:
            step = {"type": s["type"], "arg": str(s["arg"]), "delay": int(s["delay"])}
            check_step(step)
            steps.append(step)
        self.steps = steps
        st = data.get("settings", {})
        for var, key in ((self.count_var, "count"), (self.pause_var, "pause"), (self.speed_var, "speed"),
                         (self.hold_var, "hold"), (self.jitter_var, "jitter")):
            if key in st:
                var.set(str(st[key]))
        for var, key in ((self.play_key, "play_key"), (self.rec_key, "rec_key"), (self.disg_key, "disguise_key")):
            if st.get(key) in HOTKEYS:
                var.set(st[key])
        if st.get("photo") and os.path.exists(st["photo"]):
            self.load_photo(st["photo"])
        self.apply_care(data.get("care", {}))
        self.refresh_tree()

    def save_preset(self):
        path = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", "*.json")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.collect_data(), f, ensure_ascii=False, indent=1)
            self.status_var.set("Сохранено")
        except OSError as e:
            self.notify(f"Не удалось сохранить: {e}", error=True)

    def load_preset(self):
        path = filedialog.askopenfilename(filetypes=[("JSON", "*.json"), ("Все файлы", "*.*")])
        if not path:
            return
        try:
            with open(path, encoding="utf-8") as f:
                self.apply_data(json.load(f))
        except Exception as e:  # noqa: BLE001
            self.notify(f"Не удалось загрузить файл: {e}", error=True)
            return
        self.status_var.set(f"Загружено шагов: {len(self.steps)}")

    def load_config(self):
        """Автозагрузка настроек, сохранённых при прошлом закрытии программы."""
        try:
            with open(CONFIG_PATH, encoding="utf-8") as f:
                self.apply_data(json.load(f))
        except Exception:  # noqa: BLE001
            pass

    def save_config(self):
        try:
            os.makedirs(DATA_DIR, exist_ok=True)
            with open(CONFIG_PATH, "w", encoding="utf-8") as f:
                json.dump(self.collect_data(), f, ensure_ascii=False, indent=1)
        except Exception:  # noqa: BLE001
            pass

    # ---------------------------------------------------------------- выход
    def close(self):
        self.save_config()
        self.stop_evt.set()
        self.recording = False
        if self.mouse_listener:
            self.mouse_listener.stop()
        self.listener.stop()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()

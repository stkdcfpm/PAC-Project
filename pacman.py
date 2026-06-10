"""
Pac-Man Clone — single-file Pygame implementation.
Python 3.10+, Pygame only. No external assets.
"""

from __future__ import annotations

import math
import random
import sys
from enum import Enum, auto
from typing import Optional

try:
    import pygame
except ImportError:
    print("Pygame is not installed. Run:  pip install pygame")
    sys.exit(1)

# ---------------------------------------------------------------------------
# CONSTANTS
# ---------------------------------------------------------------------------
TILE = 20                      # px per tile
FPS  = 60

# Colours
C_BLACK   = (0,   0,   0)
C_WALL    = (33,  33, 222)
C_PELLET  = (255, 255, 200)
C_PPELLET = (255, 200,  50)
C_PACMAN  = (255, 220,   0)
C_TEXT    = (255, 255, 255)
C_READY   = (255, 255,   0)
C_GAMEOVER= (255,   0,   0)
C_WIN     = (0,  255,   0)
C_HUD_BG  = (0,   0,   0)

GHOST_COLORS = {
    "Blinky": (255,   0,   0),
    "Pinky":  (255, 180, 255),
    "Inky":   (0,   255, 255),
    "Clyde":  (255, 180,  50),
}
C_FRIGHTENED       = (0,   0, 200)
C_FRIGHTENED_FLASH = (255, 255, 255)

PLAYER_SPEED = 2.0    # px / frame
GHOST_SPEED  = 1.75   # px / frame normal
GHOST_SLOW   = 0.875  # tunnel / frightened speed
GHOST_FAST   = 3.5    # eaten (returning) speed

HUD_HEIGHT   = 60     # px below maze

PELLET_SCORE        = 10
POWER_PELLET_SCORE  = 50
GHOST_CHAIN_SCORES  = [200, 400, 800, 1600]

FRIGHTENED_MS       = 7_000
FRIGHTENED_FLASH_MS = 2_000   # warning flash starts this many ms before end
POWER_PELLET_BLINK  = 250     # ms per blink half-cycle

READY_MS   = 2_000
DEATH_PAUSE_MS = 1_000
EAT_FREEZE_MS  = 500
SCORE_FLOAT_MS = 1_000

# Scatter/Chase timer schedule: list of (mode, duration_ms)
MODE_SCHEDULE = [
    ("SCATTER", 7_000),
    ("CHASE",  20_000),
    ("SCATTER", 7_000),
    ("CHASE",  20_000),
    ("SCATTER", 5_000),
    ("CHASE",  -1),    # -1 = permanent
]

GHOST_RELEASE_MS = {"Blinky": 0, "Pinky": 2_000, "Inky": 5_000, "Clyde": 8_000}

LIVES_START = 3

# ---------------------------------------------------------------------------
# MAZE DEFINITION  (28 cols × 31 rows)
# # = wall   . = pellet   o = power pellet   ' ' = empty path
# - = ghost house door    P = pac-man spawn
# G = ghost house interior   T = tunnel tile
# ---------------------------------------------------------------------------
MAZE_STR = (
    "############################\n"
    "#............##............#\n"
    "#.####.#####.##.#####.####.#\n"
    "#o####.#####.##.#####.####o#\n"
    "#.####.#####.##.#####.####.#\n"
    "#..........................#\n"
    "#.####.##.########.##.####.#\n"
    "#.####.##.########.##.####.#\n"
    "#......##....##....##......#\n"
    "######.##### ## #####.######\n"
    "######.##### ## #####.######\n"
    "######.##          ##.######\n"
    "######.## ###--### ##.######\n"
    "######.## #GGGGGG# ##.######\n"
    "T      ## #GGGGGG# ##      T\n"
    "######.## #GGGGGG# ##.######\n"
    "######.## ######## ##.######\n"
    "######.##          ##.######\n"
    "######.## ######## ##.######\n"
    "######.## ######## ##.######\n"
    "#............##............#\n"
    "#.####.#####.##.#####.####.#\n"
    "#.####.#####.##.#####.####.#\n"
    "#o..##................##..o#\n"
    "###.##.##.########.##.##.###\n"
    "###.##.##.########.##.##.###\n"
    "#......##....##....##......#\n"
    "#.##########.##.##########.#\n"
    "#.##########.##.##########.#\n"
    "#P.........................#\n"
    "############################\n"
)

# Ghost spawn positions (tile col, row) — centre of ghost house
GHOST_SPAWN = {
    "Blinky": (14, 11),   # just above the door, outside
    "Pinky":  (14, 14),
    "Inky":   (12, 14),
    "Clyde":  (16, 14),
}
GHOST_HOUSE_DOOR_ROW = 12   # row of the '-' tile
GHOST_HOUSE_EXIT = (14, 11) # tile above the door to aim for when leaving

# ---------------------------------------------------------------------------
# DIRECTION HELPERS
# ---------------------------------------------------------------------------
class Dir(Enum):
    UP    = (0, -1)
    DOWN  = (0,  1)
    LEFT  = (-1, 0)
    RIGHT = (1,  0)
    NONE  = (0,  0)

    def opposite(self) -> "Dir":
        dx, dy = self.value
        for d in Dir:
            if d.value == (-dx, -dy):
                return d
        return Dir.NONE

    def angle(self) -> float:
        """Degrees for drawing, 0 = right."""
        return {Dir.RIGHT: 0, Dir.LEFT: 180, Dir.UP: 90, Dir.DOWN: 270}.get(self, 0)

KEY_TO_DIR = {
    pygame.K_UP:    Dir.UP,
    pygame.K_DOWN:  Dir.DOWN,
    pygame.K_LEFT:  Dir.LEFT,
    pygame.K_RIGHT: Dir.RIGHT,
    pygame.K_w:     Dir.UP,
    pygame.K_s:     Dir.DOWN,
    pygame.K_a:     Dir.LEFT,
    pygame.K_d:     Dir.RIGHT,
}

# ---------------------------------------------------------------------------
# MAZE
# ---------------------------------------------------------------------------
class Maze:
    def __init__(self, maze_str: str) -> None:
        rows = maze_str.strip().split("\n")
        self.rows = len(rows)
        self.cols = len(rows[0])
        self.grid: list[list[str]] = [list(r) for r in rows]
        self.pellets: set[tuple[int, int]] = set()
        self.power_pellets: set[tuple[int, int]] = set()
        self.pac_spawn: tuple[int, int] = (1, 1)
        self.tunnel_row: int = -1

        for r, row in enumerate(self.grid):
            for c, ch in enumerate(row):
                if ch == ".":
                    self.pellets.add((c, r))
                elif ch == "o":
                    self.power_pellets.add((c, r))
                elif ch == "P":
                    self.pac_spawn = (c, r)
                    self.grid[r][c] = " "   # clear spawn marker
                elif ch == "T":
                    self.tunnel_row = r
                    self.grid[r][c] = " "   # tunnel is walkable

        self.total_pellets = len(self.pellets) + len(self.power_pellets)

    def tile_at(self, col: int, row: int) -> str:
        if 0 <= row < self.rows and 0 <= col < self.cols:
            return self.grid[row][col]
        return " "   # out-of-bounds treated as open (tunnel edges)

    def is_wall(self, col: int, row: int) -> bool:
        ch = self.tile_at(col, row)
        return ch == "#"

    def is_passable(self, col: int, row: int, entering_house: bool = False) -> bool:
        ch = self.tile_at(col, row)
        if ch == "#":
            return False
        if ch == "-" and not entering_house:
            return False
        return True

    def wrap_col(self, col: int) -> int:
        return col % self.cols

    # pixel helpers
    def tile_to_px(self, col: int, row: int) -> tuple[float, float]:
        return col * TILE + TILE / 2, row * TILE + TILE / 2

    def px_to_tile(self, x: float, y: float) -> tuple[int, int]:
        return int(x // TILE), int(y // TILE)

    def draw(self, surf: pygame.Surface,
             eaten_pellets: set[tuple[int, int]],
             eaten_pp: set[tuple[int, int]],
             blink_on: bool) -> None:
        surf.fill(C_BLACK)

        for r in range(self.rows):
            for c in range(self.cols):
                ch = self.grid[r][c]
                rect = pygame.Rect(c * TILE, r * TILE, TILE, TILE)
                if ch == "#":
                    pygame.draw.rect(surf, C_WALL, rect, border_radius=3)
                elif ch == "-":
                    # ghost house door — draw as a thin pink line
                    mid_y = r * TILE + TILE // 2
                    pygame.draw.line(surf, (255, 180, 255),
                                     (c * TILE + 2, mid_y),
                                     ((c + 1) * TILE - 2, mid_y), 2)

        # Pellets
        for (c, r) in self.pellets:
            if (c, r) not in eaten_pellets:
                cx, cy = c * TILE + TILE // 2, r * TILE + TILE // 2
                pygame.draw.circle(surf, C_PELLET, (cx, cy), 2)

        # Power pellets (blinking)
        if blink_on:
            for (c, r) in self.power_pellets:
                if (c, r) not in eaten_pp:
                    cx, cy = c * TILE + TILE // 2, r * TILE + TILE // 2
                    pygame.draw.circle(surf, C_PPELLET, (cx, cy), 6)


# ---------------------------------------------------------------------------
# PLAYER
# ---------------------------------------------------------------------------
class Player:
    def __init__(self, maze: Maze) -> None:
        self.maze = maze
        self.reset()

    def reset(self) -> None:
        sc, sr = self.maze.pac_spawn
        self.x = float(sc * TILE + TILE / 2)
        self.y = float(sr * TILE + TILE / 2)
        self.dir   = Dir.NONE
        self.queued = Dir.NONE
        self.alive  = True
        self.chomp_timer = 0
        self.chomp_open  = True
        self._aligned_tile: tuple[int, int] = (-1, -1)  # last tile where we snapped

    @property
    def tile(self) -> tuple[int, int]:
        return self.maze.px_to_tile(self.x, self.y)

    def queue_dir(self, d: Dir) -> None:
        self.queued = d

    def update(self, dt_ms: float) -> None:
        speed = PLAYER_SPEED

        # Chomp animation
        self.chomp_timer += dt_ms
        if self.chomp_timer >= 200:
            self.chomp_timer = 0
            self.chomp_open = not self.chomp_open

        tc, tr = self.tile
        tx, ty = self.maze.tile_to_px(tc, tr)
        dist = math.hypot(self.x - tx, self.y - ty)

        # Apply direction change at tile centre — only once per tile entry.
        # Threshold: within (speed + 1) px so a fast entity never skips centre.
        if (tc, tr) != self._aligned_tile and dist <= speed + 1:
            self.x, self.y = tx, ty          # snap precisely to centre
            self._aligned_tile = (tc, tr)

            for candidate in (self.queued, self.dir):
                if candidate == Dir.NONE:
                    continue
                dc, dr = candidate.value
                nc, nr = tc + dc, tr + dr
                nc = self.maze.wrap_col(nc)
                if self.maze.is_passable(nc, nr):
                    self.dir = candidate
                    break
            else:
                self.dir = Dir.NONE

        if self.dir != Dir.NONE:
            dx, dy = self.dir.value
            self.x += dx * speed
            self.y += dy * speed

        # Tunnel wrap (applied after movement)
        tc2, tr2 = self.tile
        if tr2 == self.maze.tunnel_row:
            if self.x < 0:
                self.x = self.maze.cols * TILE - 1.0
                self._aligned_tile = (-1, -1)
            elif self.x >= self.maze.cols * TILE:
                self.x = 1.0
                self._aligned_tile = (-1, -1)

    def draw(self, surf: pygame.Surface) -> None:
        cx, cy = int(self.x), int(self.y)
        r = int(TILE * 0.8)

        if self.dir == Dir.NONE or not self.chomp_open:
            pygame.draw.circle(surf, C_PACMAN, (cx, cy), r)
            return

        base_angle = self.dir.angle()
        mouth_open = 30  # degrees each side

        start_a = math.radians(base_angle + mouth_open)
        end_a   = math.radians(base_angle - mouth_open)

        # Draw as polygon: centre + arc points
        points = [(cx, cy)]
        steps = 20
        angle_start = base_angle + mouth_open
        angle_span  = 360 - 2 * mouth_open
        for i in range(steps + 1):
            a = math.radians(angle_start + i * angle_span / steps)
            points.append((cx + r * math.cos(a), cy - r * math.sin(a)))
        if len(points) > 2:
            pygame.draw.polygon(surf, C_PACMAN, points)


# ---------------------------------------------------------------------------
# GHOST
# ---------------------------------------------------------------------------
class GhostMode(Enum):
    IN_HOUSE   = auto()
    LEAVING    = auto()
    SCATTER    = auto()
    CHASE      = auto()
    FRIGHTENED = auto()
    EATEN      = auto()

SCATTER_CORNERS = {
    "Blinky": (26,  0),
    "Pinky":  ( 1,  0),
    "Inky":   (26, 30),
    "Clyde":  ( 1, 30),
}

class Ghost:
    def __init__(self, name: str, maze: Maze) -> None:
        self.name  = name
        self.maze  = maze
        self.color = GHOST_COLORS[name]
        self.reset()

    def reset(self) -> None:
        sc, sr = GHOST_SPAWN[self.name]
        self.x = float(sc * TILE + TILE / 2)
        self.y = float(sr * TILE + TILE / 2)
        if self.name == "Blinky":
            self.mode = GhostMode.SCATTER
            self.dir  = Dir.LEFT
        else:
            self.mode = GhostMode.IN_HOUSE
            self.dir  = Dir.UP
        self.frightened_ms = 0
        self.chain_index   = 0     # set externally when eaten
        self._aligned_tile: tuple[int, int] = (-1, -1)

    @property
    def tile(self) -> tuple[int, int]:
        return self.maze.px_to_tile(self.x, self.y)

    def aligned(self, tolerance: float = 3.0) -> bool:
        tx, ty = self.maze.tile_to_px(*self.tile)
        return abs(self.x - tx) <= tolerance and abs(self.y - ty) <= tolerance

    def set_mode(self, new_mode: GhostMode, reverse: bool = True) -> None:
        if self.mode in (GhostMode.IN_HOUSE, GhostMode.LEAVING, GhostMode.EATEN):
            return  # don't override house/eaten logic
        if new_mode == self.mode:
            return
        if reverse:
            self.dir = self.dir.opposite()
        self.mode = new_mode

    def frighten(self, duration_ms: float) -> None:
        if self.mode in (GhostMode.IN_HOUSE, GhostMode.LEAVING, GhostMode.EATEN):
            return
        if self.mode != GhostMode.FRIGHTENED:
            self.dir = self.dir.opposite()
        self.mode = GhostMode.FRIGHTENED
        self.frightened_ms = duration_ms

    def _choose_direction(self, target: tuple[int, int],
                          entering_house: bool = False) -> Dir:
        tc, tr = self.tile
        best_dir   = self.dir
        best_dist  = float("inf")
        forbidden  = self.dir.opposite()

        for d in (Dir.UP, Dir.DOWN, Dir.LEFT, Dir.RIGHT):
            if d == forbidden:
                continue
            dc, dr = d.value
            nc, nr = tc + dc, tr + dr
            nc = self.maze.wrap_col(nc)
            if not self.maze.is_passable(nc, nr, entering_house=entering_house):
                continue
            dist = math.hypot(nc - target[0], nr - target[1])
            if dist < best_dist:
                best_dist = dist
                best_dir  = d
        return best_dir

    def _random_direction(self) -> Dir:
        tc, tr = self.tile
        forbidden = self.dir.opposite()
        options = []
        for d in (Dir.UP, Dir.DOWN, Dir.LEFT, Dir.RIGHT):
            if d == forbidden:
                continue
            dc, dr = d.value
            nc, nr = tc + dc, tr + dr
            nc = self.maze.wrap_col(nc)
            if self.maze.is_passable(nc, nr):
                options.append(d)
        return random.choice(options) if options else self.dir

    def update(self, dt_ms: float,
               player: Player,
               blinky_tile: tuple[int, int],
               global_mode: str) -> None:

        in_tunnel = (self.tile[1] == self.maze.tunnel_row)

        if self.mode == GhostMode.FRIGHTENED:
            self.frightened_ms -= dt_ms
            if self.frightened_ms <= 0:
                self.mode = GhostMode.SCATTER if global_mode == "SCATTER" else GhostMode.CHASE
                self.frightened_ms = 0

        # --- Leaving ghost house ---
        if self.mode == GhostMode.LEAVING:
            exit_tile = GHOST_HOUSE_EXIT
            tx, ty = self.maze.tile_to_px(*exit_tile)
            if abs(self.x - tx) < 2 and abs(self.y - ty) < 2:
                self.x, self.y = tx, ty
                self.mode = GhostMode.SCATTER if global_mode == "SCATTER" else GhostMode.CHASE
                self.dir  = Dir.LEFT
            else:
                # Move toward exit
                dx = tx - self.x
                dy = ty - self.y
                dist = math.hypot(dx, dy) or 1
                spd = GHOST_SPEED
                self.x += dx / dist * spd
                self.y += dy / dist * spd
            return

        # --- In house: bob up/down ---
        if self.mode == GhostMode.IN_HOUSE:
            sc, sr = GHOST_SPAWN[self.name]
            tx, ty = self.maze.tile_to_px(sc, sr)
            bob_range = TILE * 0.6
            if self.dir == Dir.UP:
                self.y -= 0.5
                if self.y < ty - bob_range:
                    self.dir = Dir.DOWN
            else:
                self.y += 0.5
                if self.y > ty + bob_range:
                    self.dir = Dir.UP
            return

        # --- Speed ---
        if self.mode == GhostMode.EATEN:
            speed = GHOST_FAST
        elif in_tunnel or self.mode == GhostMode.FRIGHTENED:
            speed = GHOST_SLOW
        else:
            speed = GHOST_SPEED

        tc, tr = self.tile
        tx, ty = self.maze.tile_to_px(tc, tr)
        dist = math.hypot(self.x - tx, self.y - ty)
        at_centre = (tc, tr) != self._aligned_tile and dist <= speed + 1

        if not at_centre:
            dx, dy = self.dir.value
            self.x += dx * speed
            self.y += dy * speed
            # Tunnel wrap
            if self.x < 0:
                self.x = self.maze.cols * TILE - 1.0
                self._aligned_tile = (-1, -1)
            elif self.x >= self.maze.cols * TILE:
                self.x = 1.0
                self._aligned_tile = (-1, -1)
            return

        # Snap to tile centre — choose next direction
        self.x, self.y = tx, ty
        self._aligned_tile = (tc, tr)

        # Choose next direction at tile centre
        if self.mode == GhostMode.EATEN:
            target = GHOST_HOUSE_EXIT
            # When we reach the exit tile, enter house
            if (tc, tr) == GHOST_HOUSE_EXIT:
                self.mode = GhostMode.LEAVING   # use LEAVING to descend into house
                spawn_c, spawn_r = GHOST_SPAWN[self.name]
                # Override: go directly to spawn
                self.mode = GhostMode.IN_HOUSE
                self.x = float(spawn_c * TILE + TILE / 2)
                self.y = float(spawn_r * TILE + TILE / 2)
                self.dir = Dir.UP
                self._aligned_tile = (-1, -1)
                return
            self.dir = self._choose_direction(target, entering_house=True)

        elif self.mode == GhostMode.FRIGHTENED:
            self.dir = self._random_direction()

        elif self.mode == GhostMode.SCATTER:
            self.dir = self._choose_direction(SCATTER_CORNERS[self.name])

        else:  # CHASE
            ptc, ptr = player.tile
            pd = player.dir.value

            if self.name == "Blinky":
                target = (ptc, ptr)

            elif self.name == "Pinky":
                target = (ptc + pd[0] * 4, ptr + pd[1] * 4)

            elif self.name == "Inky":
                pivot = (ptc + pd[0] * 2, ptr + pd[1] * 2)
                bx, by = blinky_tile
                target = (pivot[0] * 2 - bx, pivot[1] * 2 - by)

            else:  # Clyde
                dist = math.hypot(tc - ptc, tr - ptr)
                if dist > 8:
                    target = (ptc, ptr)
                else:
                    target = SCATTER_CORNERS["Clyde"]

            self.dir = self._choose_direction(target)

        dx, dy = self.dir.value
        self.x += dx * speed
        self.y += dy * speed

    def draw(self, surf: pygame.Surface, blink_on: bool) -> None:
        cx, cy = int(self.x), int(self.y)
        r = int(TILE * 0.8)

        if self.mode == GhostMode.EATEN:
            # Eyes only
            self._draw_eyes(surf, cx, cy, r, (255, 255, 255), (0, 0, 200))
            return

        if self.mode == GhostMode.FRIGHTENED:
            if self.frightened_ms < FRIGHTENED_FLASH_MS and blink_on:
                color = C_FRIGHTENED_FLASH
            else:
                color = C_FRIGHTENED
        else:
            color = self.color

        # Body: top dome + rectangular lower half
        body_rect = pygame.Rect(cx - r, cy - r // 2, r * 2, r + r // 2)
        pygame.draw.rect(surf, color, body_rect)
        pygame.draw.circle(surf, color, (cx, cy - r // 2), r)

        # Wavy bottom (3 small bumps)
        bump_r = r // 3
        for i in range(3):
            bx = cx - r + bump_r + i * bump_r * 2
            by = cy + r // 2
            pygame.draw.circle(surf, C_BLACK, (bx, by), bump_r)

        if self.mode not in (GhostMode.FRIGHTENED,):
            self._draw_eyes(surf, cx, cy, r, (255, 255, 255), (0, 0, 180))
        else:
            # Frightened face: dots for eyes, wavy mouth
            pygame.draw.circle(surf, (255, 200, 200), (cx - r // 3, cy - r // 4), 2)
            pygame.draw.circle(surf, (255, 200, 200), (cx + r // 3, cy - r // 4), 2)

    def _draw_eyes(self, surf: pygame.Surface,
                   cx: int, cy: int, r: int,
                   white: tuple, iris: tuple) -> None:
        dx, dy = self.dir.value
        for ex in (-r // 3, r // 3):
            pygame.draw.circle(surf, white, (cx + ex, cy - r // 4), r // 3)
            pygame.draw.circle(surf, iris,
                               (cx + ex + dx * (r // 5),
                                cy - r // 4 + dy * (r // 5)),
                               r // 6)


# ---------------------------------------------------------------------------
# FLOATING SCORE TEXT
# ---------------------------------------------------------------------------
class FloatText:
    def __init__(self, text: str, x: int, y: int, color: tuple,
                 font: pygame.font.Font) -> None:
        self.surf    = font.render(text, True, color)
        self.x       = x - self.surf.get_width() // 2
        self.y       = y - self.surf.get_height() // 2
        self.timer   = SCORE_FLOAT_MS

    def update(self, dt_ms: float) -> bool:
        self.timer -= dt_ms
        self.y -= 0.5
        return self.timer > 0

    def draw(self, surf: pygame.Surface) -> None:
        surf.blit(self.surf, (self.x, self.y))


# ---------------------------------------------------------------------------
# GAME STATE
# ---------------------------------------------------------------------------
class State(Enum):
    READY    = auto()
    PLAYING  = auto()
    DEATH    = auto()
    GAME_OVER= auto()
    VICTORY  = auto()

class Game:
    def __init__(self) -> None:
        self.maze   = Maze(MAZE_STR)
        if not pygame.font.get_init():
            pygame.font.init()
        self.font_sm = pygame.font.SysFont("monospace", 14, bold=True)
        self.font_md = pygame.font.SysFont("monospace", 22, bold=True)
        self.font_lg = pygame.font.SysFont("monospace", 36, bold=True)
        self.restart()

    def restart(self) -> None:
        self.eaten_pellets: set[tuple[int, int]] = set()
        self.eaten_pp:      set[tuple[int, int]] = set()
        self.score  = 0
        self.lives  = LIVES_START
        self.player = Player(self.maze)
        self.ghosts = [Ghost(n, self.maze) for n in ("Blinky", "Pinky", "Inky", "Clyde")]
        self.float_texts: list[FloatText] = []
        self.state   = State.READY
        self.state_timer = READY_MS
        self.mode_idx    = 0                 # index into MODE_SCHEDULE
        self.mode_timer  = MODE_SCHEDULE[0][1]
        self.global_mode = MODE_SCHEDULE[0][0]
        self.blink_timer = 0
        self.blink_on    = True
        self.fright_chain = 0               # ghost-eat chain counter
        self.release_timers = {n: GHOST_RELEASE_MS[n] for n in GHOST_RELEASE_MS}
        self.eat_freeze  = 0.0

    # ---- helpers -----------------------------------------------------------

    def _blinky(self) -> Ghost:
        return next(g for g in self.ghosts if g.name == "Blinky")

    def _pellets_left(self) -> int:
        return (len(self.maze.pellets) - len(self.eaten_pellets) +
                len(self.maze.power_pellets) - len(self.eaten_pp))

    def _advance_mode(self) -> None:
        self.mode_idx = min(self.mode_idx + 1, len(MODE_SCHEDULE) - 1)
        name, dur = MODE_SCHEDULE[self.mode_idx]
        self.global_mode = name
        self.mode_timer  = dur
        reverse = True
        for g in self.ghosts:
            g.set_mode(
                GhostMode.SCATTER if name == "SCATTER" else GhostMode.CHASE,
                reverse=reverse,
            )

    # ---- update ------------------------------------------------------------

    def update(self, dt_ms: float) -> None:
        self.blink_timer += dt_ms
        if self.blink_timer >= POWER_PELLET_BLINK:
            self.blink_timer = 0
            self.blink_on = not self.blink_on

        if self.state == State.READY:
            self.state_timer -= dt_ms
            if self.state_timer <= 0:
                self.state = State.PLAYING
            return

        if self.state in (State.GAME_OVER, State.VICTORY):
            return

        if self.state == State.DEATH:
            self.state_timer -= dt_ms
            if self.state_timer <= 0:
                self.lives -= 1
                if self.lives <= 0:
                    self.state = State.GAME_OVER
                else:
                    self.player.reset()
                    for g in self.ghosts:
                        g.reset()
                    self.fright_chain = 0
                    self.state       = State.READY
                    self.state_timer = READY_MS
            return

        # Eat-freeze pause
        if self.eat_freeze > 0:
            self.eat_freeze -= dt_ms
            return

        # Global scatter/chase timer
        if self.mode_timer > 0:
            self.mode_timer -= dt_ms
            if self.mode_timer <= 0:
                self._advance_mode()

        # Release ghosts
        for name, t in list(self.release_timers.items()):
            if t > 0:
                self.release_timers[name] = t - dt_ms
                if self.release_timers[name] <= 0:
                    for g in self.ghosts:
                        if g.name == name and g.mode == GhostMode.IN_HOUSE:
                            g.mode = GhostMode.LEAVING

        blinky_tile = self._blinky().tile
        self.player.update(dt_ms)

        for g in self.ghosts:
            g.update(dt_ms, self.player, blinky_tile, self.global_mode)

        # Pellet collection
        ptile = self.player.tile
        if ptile in self.maze.pellets and ptile not in self.eaten_pellets:
            self.eaten_pellets.add(ptile)
            self.score += PELLET_SCORE

        if ptile in self.maze.power_pellets and ptile not in self.eaten_pp:
            self.eaten_pp.add(ptile)
            self.score += POWER_PELLET_SCORE
            self.fright_chain = 0
            for g in self.ghosts:
                g.frighten(FRIGHTENED_MS)

        # Victory?
        if self._pellets_left() == 0:
            self.state = State.VICTORY
            return

        # Ghost collisions
        for g in self.ghosts:
            pc, pr = self.player.tile
            gc, gr = g.tile
            dist = math.hypot(self.player.x - g.x, self.player.y - g.y)
            if dist > TILE:
                continue

            if g.mode == GhostMode.FRIGHTENED:
                pts = GHOST_CHAIN_SCORES[min(self.fright_chain, 3)]
                self.fright_chain += 1
                self.score += pts
                self.float_texts.append(
                    FloatText(str(pts), int(g.x), int(g.y), C_PPELLET, self.font_sm)
                )
                g.mode = GhostMode.EATEN
                self.eat_freeze = EAT_FREEZE_MS

            elif g.mode not in (GhostMode.EATEN, GhostMode.IN_HOUSE,
                                 GhostMode.LEAVING):
                self.state       = State.DEATH
                self.state_timer = DEATH_PAUSE_MS

        # Float texts
        self.float_texts = [t for t in self.float_texts if t.update(dt_ms)]

    # ---- draw --------------------------------------------------------------

    def draw(self, surf: pygame.Surface) -> None:
        self.maze.draw(surf, self.eaten_pellets, self.eaten_pp, self.blink_on)

        self.player.draw(surf)
        for g in self.ghosts:
            g.draw(surf, self.blink_on)

        for ft in self.float_texts:
            ft.draw(surf)

        # HUD
        hud_y = self.maze.rows * TILE
        hud_rect = pygame.Rect(0, hud_y, self.maze.cols * TILE, HUD_HEIGHT)
        pygame.draw.rect(surf, C_HUD_BG, hud_rect)

        score_surf = self.font_sm.render(f"SCORE: {self.score}", True, C_TEXT)
        surf.blit(score_surf, (8, hud_y + 8))

        # Lives as small pac-man icons
        for i in range(self.lives):
            lx = self.maze.cols * TILE - (i + 1) * 28
            ly = hud_y + 10
            points = [(lx + 10, ly + 8)]
            for step in range(25):
                a = math.radians(30 + step * (300 / 24))
                points.append((lx + 10 + 9 * math.cos(a), ly + 8 - 9 * math.sin(a)))
            if len(points) > 2:
                pygame.draw.polygon(surf, C_PACMAN, points)

        # Overlay messages
        cx = self.maze.cols * TILE // 2
        my = self.maze.rows * TILE // 2

        if self.state == State.READY:
            self._centered(surf, "READY!", self.font_md, C_READY, cx, my)

        elif self.state == State.GAME_OVER:
            self._centered(surf, "GAME OVER", self.font_lg, C_GAMEOVER, cx, my - 30)
            self._centered(surf, f"SCORE: {self.score}", self.font_md, C_TEXT, cx, my + 10)
            self._centered(surf, "R = restart   ESC = quit", self.font_sm, C_TEXT, cx, my + 45)

        elif self.state == State.VICTORY:
            self._centered(surf, "YOU WIN!", self.font_lg, C_WIN, cx, my - 30)
            self._centered(surf, f"SCORE: {self.score}", self.font_md, C_TEXT, cx, my + 10)
            self._centered(surf, "R = restart   ESC = quit", self.font_sm, C_TEXT, cx, my + 45)

    def _centered(self, surf: pygame.Surface, text: str,
                  font: pygame.font.Font, color: tuple,
                  cx: int, cy: int) -> None:
        s = font.render(text, True, color)
        surf.blit(s, (cx - s.get_width() // 2, cy - s.get_height() // 2))


# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------
def main() -> None:
    try:
        pygame.init()
        pygame.display.set_caption("Pac-Man")

        maze_tmp = Maze(MAZE_STR)
        WIN_W = maze_tmp.cols * TILE
        WIN_H = maze_tmp.rows * TILE + HUD_HEIGHT
        screen = pygame.display.set_mode((WIN_W, WIN_H))
        clock  = pygame.time.Clock()

        game = Game()

        running = True
        while running:
            dt_ms = clock.tick(FPS)

            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                elif event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_ESCAPE:
                        running = False
                    elif event.key == pygame.K_r:
                        if game.state in (State.GAME_OVER, State.VICTORY):
                            game.restart()
                    elif event.key in KEY_TO_DIR:
                        game.player.queue_dir(KEY_TO_DIR[event.key])

            game.update(float(dt_ms))
            game.draw(screen)
            pygame.display.flip()

    except Exception as exc:
        print(f"Fatal error: {exc}")
        raise
    finally:
        pygame.quit()


if __name__ == "__main__":
    main()

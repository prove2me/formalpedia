-- Prove2me | solution 1 for WilliamsonShmoys.face_count_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T02:33:12.388256+00:00
-- url     : https://prove2.me/submissions/24171e91-1432-4b80-b0b3-69a5462c7073

import Mathlib

set_option autoImplicit false

theorem solution
    (n e f : ℕ)
    (hEuler : n + f = e + 2)
    (hFaces : 3 * f = 2 * e) :
    e + 6 = 3 * n := by omega

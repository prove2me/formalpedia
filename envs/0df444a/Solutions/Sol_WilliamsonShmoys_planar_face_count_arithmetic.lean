-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T03:18:20.209421+00:00
-- url     : https://prove2.me/submissions/e652b133-bcd2-4df3-bb35-3bd8eb465335

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : ℕ)
    (hn : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hPerimeter : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by
  omega
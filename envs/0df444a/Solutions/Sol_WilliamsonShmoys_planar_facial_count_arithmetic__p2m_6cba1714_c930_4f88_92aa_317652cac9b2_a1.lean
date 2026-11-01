-- Prove2me | solution 1 for WilliamsonShmoys.planar_facial_count_arithmetic__p2m_6cba1714_c930_4f88_92aa_317652cac9b2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:08:42.602205+00:00
-- url     : https://prove2.me/submissions/ddd64894-7d72-4566-a3be-7341685c24c4

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : Nat)
    (heuler : n + f = m + 2)
    (htri : 3 * f = 2 * m) :
    3 * n <= m + 6 := by
  omega
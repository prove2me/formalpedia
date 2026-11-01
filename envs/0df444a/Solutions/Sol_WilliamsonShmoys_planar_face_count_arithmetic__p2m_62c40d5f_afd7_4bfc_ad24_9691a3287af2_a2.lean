-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_count_arithmetic__p2m_62c40d5f_afd7_4bfc_ad24_9691a3287af2_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:43.961721+00:00
-- url     : https://prove2.me/submissions/cc1f346e-de8d-4650-a679-c6badb4e0bbe

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : Nat) (hn : 3 <= n) (heuler : n + f = m + 2)
    (hdegree : 3 * f <= 2 * m) :
    m + 6 <= 3 * n := by
  omega
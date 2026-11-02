-- Prove2me | solution 1 for WilliamsonShmoys.planar_euler_edge_arithmetic__p2m_00ee0ef8_811a_4a39_b8c0_1ed175b9b4ef_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:31:07.60312+00:00
-- url     : https://prove2.me/submissions/1c0a2ffd-7a2d-4ae5-9711-be37c22ec260

import Mathlib

set_option autoImplicit false

theorem solution
    (n m f : ℕ)
    (hn : 3 ≤ n)
    (heuler : n + f = m + 2)
    (hboundary : 3 * f ≤ 2 * m) :
    m + 6 ≤ 3 * n := by
  omega
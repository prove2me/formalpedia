-- Prove2me | solution 1 for WilliamsonShmoys.euler_triangulation_edge_arithmetic__p2m_306301a2_72f6_4d8f_a2c9_6046e69fec66_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:46.76867+00:00
-- url     : https://prove2.me/submissions/13150131-a336-4631-b3aa-c9c045ab9301

import Mathlib

theorem solution
    (n e f : ℕ)
    (hn : 3 <= n)
    (hEuler : (n : ℤ) - (e : ℤ) + (f : ℤ) = 2)
    (htri : 3 * f = 2 * e) :
    e + 6 <= 3 * n := by
  omega
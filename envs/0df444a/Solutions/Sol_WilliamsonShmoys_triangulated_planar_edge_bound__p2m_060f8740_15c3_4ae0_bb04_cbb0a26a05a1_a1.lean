-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_planar_edge_bound__p2m_060f8740_15c3_4ae0_bb04_cbb0a26a05a1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:09:02.386417+00:00
-- url     : https://prove2.me/submissions/9d998e18-db2c-4329-a7e6-37a26464fc27

import Mathlib

set_option autoImplicit false

theorem solution (n m f : Nat) (hn : 3 <= n) (hEuler : n + f = m + 2)
    (htri : 3 * f = 2 * m) : 3 * n <= m + 6 := by
  omega
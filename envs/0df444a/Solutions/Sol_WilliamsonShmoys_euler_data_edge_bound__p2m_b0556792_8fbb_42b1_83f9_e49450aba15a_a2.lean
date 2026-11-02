-- Prove2me | solution 1 for WilliamsonShmoys.euler_data_edge_bound__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T11:37:21.859799+00:00
-- url     : https://prove2.me/submissions/626ece9d-1489-4870-960a-7421b5c9e17a

import Mathlib

theorem solution
    (n e f l : ℕ)
    (hn : 3 ≤ n)
    (hEuler : n + f = e + 2)
    (hSides : l = 2 * e)
    (hFaces : 3 * f ≤ l) :
    e + 6 ≤ 3 * n := by
  omega
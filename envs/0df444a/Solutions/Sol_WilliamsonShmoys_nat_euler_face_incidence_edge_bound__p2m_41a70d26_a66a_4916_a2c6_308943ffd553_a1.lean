-- Prove2me | solution 1 for WilliamsonShmoys.nat_euler_face_incidence_edge_bound__p2m_41a70d26_a66a_4916_a2c6_308943ffd553_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:04:10.04655+00:00
-- url     : https://prove2.me/submissions/866c566a-051f-4aac-9a82-54e3c8ca5774

import Mathlib

set_option autoImplicit false

theorem solution (n m f : Nat) (hn : 3 ≤ n)
    (heuler : n + f = m + 2)
    (hinc : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by
  omega
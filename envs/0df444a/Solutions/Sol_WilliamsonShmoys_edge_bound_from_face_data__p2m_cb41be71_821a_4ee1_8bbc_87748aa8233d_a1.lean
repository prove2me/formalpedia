-- Prove2me | solution 1 for WilliamsonShmoys.edge_bound_from_face_data__p2m_cb41be71_821a_4ee1_8bbc_87748aa8233d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:06:19.636939+00:00
-- url     : https://prove2.me/submissions/f3835534-3649-4078-974f-34dd088f6e2a

import Mathlib

set_option autoImplicit false

theorem solution (v e f : ℕ) (heuler : v + f = e + 2) (hfaces : 3 * f ≤ 2 * e) : e + 6 ≤ 3 * v := by
  omega
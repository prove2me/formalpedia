-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_bound_from_euler_and_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:43:04.65699+00:00
-- url     : https://prove2.me/submissions/0108d51c-3c79-4788-a531-ee398b9a2f7f

import Mathlib

set_option autoImplicit false

theorem solution (E V f : Nat) (heuler : E + 2 = V + f) (hbound : E + 6 <= 3 * V) : 3 * f <= 2 * E := by
  omega
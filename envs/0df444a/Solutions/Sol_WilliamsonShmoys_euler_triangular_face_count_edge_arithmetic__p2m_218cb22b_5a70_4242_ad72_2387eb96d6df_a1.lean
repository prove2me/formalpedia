-- Prove2me | solution 1 for WilliamsonShmoys.euler_triangular_face_count_edge_arithmetic__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:52:53.963758+00:00
-- url     : https://prove2.me/submissions/83c21452-bf06-4787-b86d-d10fb77ba438

import Mathlib

set_option autoImplicit false

theorem solution
    (f n e : ℕ)
    (hEuler : f + n = e + 2)
    (hIncidence : 3 * f = 2 * e) :
    3 * n ≤ e + 6 := by
  omega
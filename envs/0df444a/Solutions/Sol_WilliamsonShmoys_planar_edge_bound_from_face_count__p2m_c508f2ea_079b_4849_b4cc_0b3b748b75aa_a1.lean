-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound_from_face_count__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:16:34.675929+00:00
-- url     : https://prove2.me/submissions/b8594357-7536-4ddd-bbd0-035208a726b0

import Mathlib

set_option autoImplicit false

theorem solution
    (n e f : Nat)
    (hn : 3 ≤ n)
    (heuler : e + 2 = n + f)
    (hdegree : 3 * f ≤ 2 * e) :
    e ≤ 3 * n - 6 := by
  omega
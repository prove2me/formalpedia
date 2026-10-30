-- Prove2me | solution 1 for WilliamsonShmoys.planar_face_equations_imply_edge_count__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:58:36.399067+00:00
-- url     : https://prove2.me/submissions/d64912a5-5a38-424d-94cd-cf781c0720f2

import Mathlib

set_option autoImplicit false

theorem solution (n m f : Nat) (hEuler : n + f = m + 2) (hTri : 3 * f = 2 * m) :
    m + 6 = 3 * n := by
  omega
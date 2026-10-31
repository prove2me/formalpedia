-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:19:02.796234+00:00
-- url     : https://prove2.me/submissions/a876d2b7-1459-4857-8555-cd27d96fab7d

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧ 3 * f = 2 * K.edgeSet.ncard :=
  WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3 K hK hV hmax

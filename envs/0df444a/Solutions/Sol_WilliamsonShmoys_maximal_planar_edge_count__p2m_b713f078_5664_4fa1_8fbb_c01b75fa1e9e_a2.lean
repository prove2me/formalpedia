-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_b713f078_5664_4fa1_8fbb_c01b75fa1e9e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:49:39.29569+00:00
-- url     : https://prove2.me/submissions/d7c18e95-136d-4aea-98b0-053ea9140eda

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_55ddcaf2_84d6_4a74_8795_9ad03c9060dc_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V,
      H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition__p2m_55ddcaf2_84d6_4a74_8795_9ad03c9060dc_a1
      H hH hmax hV
  omega
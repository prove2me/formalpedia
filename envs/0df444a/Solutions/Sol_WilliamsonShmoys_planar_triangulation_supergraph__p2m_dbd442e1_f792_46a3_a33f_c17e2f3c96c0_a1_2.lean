-- Prove2me | solution 2 for WilliamsonShmoys.planar_triangulation_supergraph__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:10:39.742046+00:00
-- url     : https://prove2.me/submissions/5175993b-66b9-4f79-81d9-cbd460772a54

import Theorems.Thm_WilliamsonShmoys_planar_drawing_supergraph_exact_edge_count_9ac50290_da1b_42d2_8798_1bec9d81b4c1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_supergraph_exact_edge_count_9ac50290_da1b_42d2_8798_1bec9d81b4c1 H hH hV

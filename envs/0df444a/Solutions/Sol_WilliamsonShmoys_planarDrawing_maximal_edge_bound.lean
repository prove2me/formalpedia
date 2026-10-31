-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawing_maximal_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:56:22.759698+00:00
-- url     : https://prove2.me/submissions/fac9cb05-804f-4849-8c62-97143b832f34

import Theorems.Thm_WilliamsonShmoys_planarDrawing_maximal_edge_bound__p2m_523c1acd_d899_4f39_911b_962863474905_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hP : HasPlanarDrawingOn P)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ Q : SimpleGraph V, P ≤ Q → HasPlanarDrawingOn Q →
      Q.edgeSet.ncard ≤ P.edgeSet.ncard) :
    3 * Fintype.card V ≤ P.edgeSet.ncard + 6 :=
  WilliamsonShmoys.planarDrawing_maximal_edge_bound__p2m_523c1acd_d899_4f39_911b_962863474905_a4 P hP hCard hMax

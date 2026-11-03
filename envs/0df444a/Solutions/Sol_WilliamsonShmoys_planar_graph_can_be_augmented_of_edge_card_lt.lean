-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_can_be_augmented_of_edge_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T22:19:50.538178+00:00
-- url     : https://prove2.me/submissions/f0280ae5-5fab-43b7-88eb-7e407c89db48

import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_extension

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : P.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ Q : SimpleGraph V,
      P.edgeSet ⊂ Q.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn Q :=
  WilliamsonShmoys.planar_drawing_edge_count_extension P hP hV hcard
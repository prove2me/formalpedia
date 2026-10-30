-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_card_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:17:57.152169+00:00
-- url     : https://prove2.me/submissions/fc4b04cf-9476-4d7b-8d78-c487f55ad8c0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_sparse_graph_has_planar_strict_supergraph__p2m_781b7780_35b2_4c7b_8f6f_87d1d7202df9_a1

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hMax : forall R : SimpleGraph V,
      (forall u v, T.Adj u v -> R.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn R -> R = T) :
    3 * Fintype.card V - 6 <= T.edgeSet.ncard := by
  by_contra h
  have hSparse : T.edgeSet.ncard < 3 * Fintype.card V - 6 := Nat.lt_of_not_ge h
  obtain ⟨R, hTR, hRT, hR⟩ :=
    WilliamsonShmoys.planar_drawing_sparse_graph_has_planar_strict_supergraph__p2m_781b7780_35b2_4c7b_8f6f_87d1d7202df9_a1
      T hCard hT hSparse
  exact hRT (hMax R hTR hR)
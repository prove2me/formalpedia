-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_of_maximal_planar_drawing_9e31d0d7_bedf_4a6b_a6d6_c2c0226ce7c3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:01:37.207518+00:00
-- url     : https://prove2.me/submissions/ea2c88da-fee1-4bac-a9df-5e819be62b15

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_card_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_card_lower_bound

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
    T.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  apply Nat.le_antisymm
  · exact WilliamsonShmoys.planar_edge_card_upper_bound T hCard hT
  · exact WilliamsonShmoys.maximal_planar_drawing_edge_card_lower_bound T hCard hT hMax
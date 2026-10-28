-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_induced_edge_bound_small
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T02:54:25.669699+00:00
-- url     : https://prove2.me/submissions/7ae1dfb6-d367-4a89-973d-a58170b6a0ad

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (S : Finset V)
    (hNonempty : S.Nonempty)
    (hSmall : S.card < 3) :
    (H.induce (↑S : Set V)).edgeSet.ncard ≤ S.card / 2 := by
  classical
  let G := H.induce (↑S : Set V)
  have hCardPos : 0 < S.card := Finset.card_pos.mpr hNonempty
  have hCard : S.card = 1 ∨ S.card = 2 := by omega
  have hEdgeCard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← Set.fintypeCard_eq_ncard, G.card_edgeSet]
  have hEdgeBound : G.edgeFinset.card ≤ S.card.choose 2 := by
    simpa using G.card_edgeFinset_le_card_choose_two
  change G.edgeSet.ncard ≤ S.card / 2
  rw [hEdgeCard]
  rcases hCard with h | h
  · rw [h] at hEdgeBound ⊢
    norm_num at hEdgeBound ⊢
    omega
  · rw [h] at hEdgeBound ⊢
    norm_num at hEdgeBound ⊢
    omega
-- Prove2me | solution 1 for WilliamsonShmoys.connected_small_piece_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:47:00.710149+00:00
-- url     : https://prove2.me/submissions/2170e218-41c2-4f94-a392-4f3dc9dca17a

import Mathlib
theorem solution
    {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (S : Finset V)
    (hconn : (G.induce (↑S : Set V)).Connected)
    (hpos : 0 < S.card) (hlt : S.card < 3) :
    (G.induce (↑S : Set V)).edgeSet.ncard + 3 ≤ 3 * S.card := by
  classical
  have h1 : (G.induce (↑S : Set V)).edgeSet.ncard
      = (G.induce (↑S : Set V)).edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset]
  have h2 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G.induce (↑S : Set V))
  have h3 : Fintype.card (↑(↑S : Set V)) = S.card := by simp
  rw [h3] at h2
  rw [h1]
  interval_cases hS : S.card <;> simp at h2 ⊢ <;> omega

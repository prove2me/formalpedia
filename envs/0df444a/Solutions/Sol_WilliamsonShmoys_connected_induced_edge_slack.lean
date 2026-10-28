-- Prove2me | solution 1 for WilliamsonShmoys.connected_induced_edge_slack
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T11:38:34.71254+00:00
-- url     : https://prove2.me/submissions/5bc81585-1805-4a5b-bf22-c20817a1fe9b

import Mathlib
namespace WilliamsonShmoys
theorem _root_.solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (S : Finset V)
    (hBound : 3 <= S.card -> (L.induce S).Connected ->
      ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6)
    (hConn : (L.induce S).Connected) :
    (((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 3) ∧
      (3 <= S.card -> ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6) := by
  refine ⟨?_, fun h3 => hBound h3 hConn⟩
  by_cases h3 : 3 ≤ S.card
  · have := hBound h3 hConn; linarith
  · classical
    have hs := SimpleGraph.card_edgeFinset_le_card_choose_two (G := L.induce (S : Set V))
    have he : (L.induce (S : Set V)).edgeFinset.card = (L.induce (S : Set V)).edgeSet.ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    have hc : Fintype.card (↑(S : Set V)) = S.card := by simp
    rw [he, hc] at hs
    have hpos : 0 < S.card := by
      obtain ⟨⟨v, hv⟩⟩ := hConn.nonempty; exact Finset.card_pos.mpr ⟨v, hv⟩
    interval_cases h : S.card
    · rw [show Nat.choose 1 2 = 0 from rfl] at hs; omega
    · rw [show Nat.choose 2 2 = 1 from rfl] at hs; omega
end WilliamsonShmoys


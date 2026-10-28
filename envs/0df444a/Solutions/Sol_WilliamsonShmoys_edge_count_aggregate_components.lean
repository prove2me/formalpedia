-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_aggregate_components
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:35:47.728994+00:00
-- url     : https://prove2.me/submissions/48744472-8efd-4326-ac93-cf5c546a5975

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (C : Finset (Finset V))
    (hCard : 3 <= Fintype.card V)
    (hConnectedBounds :
      ∀ S : Finset V, 3 <= S.card → (L.induce S).Connected →
        ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6)
    (hCardSum : ∑ S ∈ C, S.card = Fintype.card V)
    (hEdgeSum :
      (L.edgeSet.ncard : Int) = ∑ S ∈ C, ((L.induce S).edgeSet.ncard : Int))
    (hConnected : ∀ S ∈ C, (L.induce S).Connected) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by
  classical
  have hsmall : ∀ S ∈ C, ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 3 := by
    intro S hS
    rcases Nat.lt_or_ge S.card 3 with h | h
    · have hne : Nonempty (↥(S : Set V)) := (hConnected S hS).nonempty
      have hpos : 0 < S.card := by
        obtain ⟨⟨x, hx⟩⟩ := hne
        exact Finset.card_pos.mpr ⟨x, hx⟩
      have h1 := SimpleGraph.card_edgeFinset_le_card_choose_two (G := L.induce (S : Set V))
      have h2 : (L.induce (S : Set V)).edgeSet.ncard = (L.induce (S : Set V)).edgeFinset.card := by
        rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
      have h3 : Fintype.card (↥(S : Set V)) = S.card := by simp
      rw [h3] at h1
      have h4 : (L.induce (S : Set V)).edgeSet.ncard ≤ S.card.choose 2 := h2 ▸ h1
      interval_cases hc : S.card
      · simp at h4; omega
      · have e : Nat.choose 2 2 = 1 := rfl; rw [e] at h1 h4; omega
    · have := hConnectedBounds S h (hConnected S hS); omega
  rw [hEdgeSum]
  have hcs : (∑ S ∈ C, (S.card : Int)) = (Fintype.card V : Int) := by exact_mod_cast hCardSum
  rcases Nat.lt_or_ge C.card 2 with h | h
  · interval_cases hc : C.card
    · rw [Finset.card_eq_zero] at hc; subst hc; simp at hCardSum; omega
    · obtain ⟨S, rfl⟩ := Finset.card_eq_one.mp hc
      simp only [Finset.sum_singleton] at hCardSum ⊢
      have := hConnectedBounds S (by omega) (hConnected S (by simp))
      rw [hCardSum] at this; exact this
  · calc ∑ S ∈ C, ((L.induce S).edgeSet.ncard : Int)
        ≤ ∑ S ∈ C, (3 * (S.card : Int) - 3) := Finset.sum_le_sum hsmall
      _ = 3 * (Fintype.card V : Int) - 3 * C.card := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcs]; simp; ring
      _ ≤ 3 * (Fintype.card V : Int) - 6 := by
        have : (2 : Int) ≤ C.card := by exact_mod_cast h
        omega

-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_below_complete_has_nonadjacent_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:12:02.587157+00:00
-- url     : https://prove2.me/submissions/7cc6f9e3-719f-4512-a75a-d006ff84fdab

import Mathlib

set_option autoImplicit false


theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hE : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v := by
  classical
  by_contra h
  push_neg at h
  have htop : G = ⊤ := by
    ext u v
    simp only [SimpleGraph.top_adj]
    exact ⟨fun h' => G.ne_of_adj h', fun hne => h u v hne⟩
  subst htop
  have hc := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V)
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] at hc
  rw [hc, Nat.choose_two_right] at hE
  have h1 : 3 * Fintype.card V - 6 ≤ Fintype.card V * (Fintype.card V - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card V = k + 3 := ⟨Fintype.card V - 3, by omega⟩
    rw [hk]
    have e1 : (k + 3 - 1) = k + 2 := by omega
    have e2 : 3 * (k + 3) - 6 = 3 * k + 3 := by omega
    rw [e1, e2]
    nlinarith [Nat.le_mul_self k]
  omega

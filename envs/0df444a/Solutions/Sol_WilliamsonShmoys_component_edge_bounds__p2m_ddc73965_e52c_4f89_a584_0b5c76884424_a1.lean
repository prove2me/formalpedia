-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T13:34:56.669363+00:00
-- url     : https://prove2.me/submissions/a8ebbe70-6bc8-4057-83f3-6a86472c9d09

import Mathlib

set_option autoImplicit false

/-- Componentwise consequences of a local edge bound: small components span at most one edge,
and large components satisfy the additive local bound. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hLocal : ∀ (S : Finset V), 3 ≤ S.card →
      (L.induce (↑S : Set V)).Connected →
      (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) :
    (∀ c : L.ConnectedComponent, c.supp.ncard ≤ 2 →
        (L.induce c.supp).edgeSet.ncard ≤ 1) ∧
      (∀ c : L.ConnectedComponent, 3 ≤ c.supp.ncard →
        (L.induce c.supp).edgeSet.ncard + 6 ≤ 3 * c.supp.ncard) := by
  classical
  constructor
  · intro c hsmall
    have hcard : Fintype.card c.supp ≤ 2 := by
      have h' : c.supp.toFinset.card ≤ 2 := by
        rwa [Set.ncard_eq_toFinset_card'] at hsmall
      rwa [Set.toFinset_card] at h'
    have h1 : (L.induce c.supp).edgeFinset.card ≤ (Fintype.card c.supp).choose 2 :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
    have h2 : (L.induce c.supp).edgeSet.ncard = (L.induce c.supp).edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [h2]
    have hchoose : (Fintype.card c.supp).choose 2 ≤ 1 := by
      rcases le_or_gt (Fintype.card c.supp) 1 with h | h
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        omega
      · have h2 : Fintype.card c.supp = 2 := by omega
        rw [h2]
        norm_num
    omega
  · intro c hc
    have hfin : c.supp.Finite := Set.toFinite _
    obtain ⟨S, hS⟩ : ∃ S : Finset V, (↑S : Set V) = c.supp :=
      ⟨hfin.toFinset, hfin.coe_toFinset⟩
    have hScard : S.card = c.supp.ncard := by
      rw [← Set.ncard_coe_finset S, hS]
    have hconn : (L.induce (↑S : Set V)).Connected := by
      rw [hS]
      exact c.connected_toSimpleGraph
    have h3 : 3 ≤ S.card := by omega
    have h := hLocal S h3 hconn
    rw [hS, hScard] at h
    exact h

-- Prove2me | solution 2 for WilliamsonShmoys.finite_connected_component_partition__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T16:10:26.498014+00:00
-- url     : https://prove2.me/submissions/8f12cbda-5be5-4cd6-92e2-53076341fadc

import Mathlib
import Theorems.Thm_WilliamsonShmoys_connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1

set_option autoImplicit false

private theorem edge_ncard_eq_card {α : Type} (G : SimpleGraph α) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  exact Set.ncard_eq_toFinset_card' _

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ C : Finset (Finset V),
      (∀ B ∈ C, 0 < B.card) ∧
      (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
        Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) ∧
      (∀ v : V, ∃ B ∈ C, v ∈ B) ∧
      Fintype.card V = ∑ B ∈ C, B.card ∧
      (∀ B ∈ C,
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).Connected) ∧
      (∀ B ∈ C, B.card = 1 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card = 0) ∧
      (∀ B ∈ C, B.card = 2 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card ≤ 1) ∧
      N.edgeFinset.card =
        ∑ B ∈ C,
          (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _;
           (N.induce (↑B : Set V)).edgeFinset.card)) := by
  classical
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨C, huniq, hcard, hedges, hconn, hsmall⟩ :=
    WilliamsonShmoys.connected_component_partition_data__p2m_2aff762d_92be_4091_96b6_7b0d6e06700b_a1 N
  refine ⟨C, ?_, ?_, ?_, hcard, hconn, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨⟨v, hv⟩⟩ := (hconn B hB).nonempty
    exact Finset.card_pos.mpr ⟨v, hv⟩
  · intro B₁ hB₁ B₂ hB₂ hne
    apply Set.disjoint_left.mpr
    intro v hv₁ hv₂
    obtain ⟨W, hW, hWuniq⟩ := huniq v
    have h₁ : B₁ = W := hWuniq B₁ ⟨hB₁, hv₁⟩
    have h₂ : B₂ = W := hWuniq B₂ ⟨hB₂, hv₂⟩
    exact hne (h₁.trans h₂.symm)
  · intro v
    obtain ⟨W, hW, -⟩ := huniq v
    exact ⟨W, hW.1, hW.2⟩
  · intro B hB hb
    letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
    change (N.induce (↑B : Set V)).edgeFinset.card = 0
    rw [← edge_ncard_eq_card]
    have h := hsmall B hB (by omega)
    omega
  · intro B hB hb
    letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
    change (N.induce (↑B : Set V)).edgeFinset.card ≤ 1
    rw [← edge_ncard_eq_card]
    have h := hsmall B hB (by omega)
    omega
  · calc
      N.edgeFinset.card = N.edgeSet.ncard := (edge_ncard_eq_card N).symm
      _ = ∑ B ∈ C, (N.induce (↑B : Set V)).edgeSet.ncard := hedges
      _ = ∑ B ∈ C,
          (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _;
           (N.induce (↑B : Set V)).edgeFinset.card) := by
        apply Finset.sum_congr rfl
        intro B hB
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        change (N.induce (↑B : Set V)).edgeSet.ncard =
          (N.induce (↑B : Set V)).edgeFinset.card
        exact edge_ncard_eq_card _

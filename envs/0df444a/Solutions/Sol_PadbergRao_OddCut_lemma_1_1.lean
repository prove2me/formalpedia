-- Prove2me | solution 1 for PadbergRao.OddCut.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:47:34.324003+00:00
-- url     : https://prove2.me/submissions/631556e8-3254-4917-a3a4-3b5fa4bf6101

import Definitions.Def_PadbergRao_OddCut_IsOddMinCut
import Definitions.Def_PadbergRao_OddCut_IsMinOddPairCut

open Finset
open PadbergRao.OddCut

set_option autoImplicit false

private lemma cut_compl {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hs : ∀ i j, c i j = c j i) (S : Finset V) :
    cutCapacity c Sᶜ = cutCapacity c S := by
  simp only [cutCapacity, compl_compl]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => hs j i

private lemma cut_sum {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (S : Finset V) :
    cutCapacity c S = ∑ i, ∑ j, if i ∈ S ∧ j ∉ S then c i j else 0 := by
  simp only [ite_and, sum_ite_irrel, sum_const_zero]
  rw [sum_ite_mem]
  simp only [univ_inter]
  apply sum_congr rfl
  intro i _
  rw [← sum_filter]
  congr 1
  ext j
  simp

private lemma cut_submodular {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hn : ∀ i j, 0 ≤ c i j) (A B : Finset V) :
    cutCapacity c (A ∩ B) + cutCapacity c (A ∪ B) ≤
      cutCapacity c A + cutCapacity c B := by
  simp only [cut_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;>
    by_cases hjA : j ∈ A <;> by_cases hjB : j ∈ B <;>
    simp [hiA, hiB, hjA, hjB] <;> linarith [hn i j]

private lemma card_partition {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset V) : (A ∩ B).card + (Aᶜ ∩ B).card = B.card := by
  have hd : Disjoint (A ∩ B) (Aᶜ ∩ B) := by
    apply disjoint_left.mpr
    simp only [mem_inter, mem_compl]
    tauto
  have hu : (A ∩ B) ∪ (Aᶜ ∩ B) = B := by ext; simp; tauto
  rw [← card_union_of_disjoint hd, hu]

private lemma odd_compl {V : Type*} [Fintype V] [DecidableEq V]
    (odd A : Finset V) (he : Even odd.card) (hA : IsOddSet odd A) :
    IsOddSet odd Aᶜ := by
  have h := card_partition A odd
  unfold IsOddSet at *
  rw [Nat.even_iff] at he
  rw [Nat.odd_iff] at hA ⊢
  omega

private lemma odd_sep {V : Type*} [Fintype V] [DecidableEq V]
    (odd A : Finset V) (he : Even odd.card) (hA : IsOddSet odd A) :
    SeparatesOddPair odd A := by
  have hAc := odd_compl odd A he hA
  obtain ⟨p, hp⟩ := card_pos.mp hA.pos
  obtain ⟨q, hq⟩ := card_pos.mp hAc.pos
  exact ⟨p, (mem_inter.mp hp).2, q, (mem_inter.mp hq).2,
    (mem_inter.mp hp).1, mem_compl.mp (mem_inter.mp hq).1⟩

private lemma min_odd_exists {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (odd : Finset V) (hne : odd.Nonempty) :
    ∃ A : Finset V, IsOddMinCut c odd A := by
  classical
  obtain ⟨v, hv⟩ := hne
  have hv' : IsOddSet odd {v} := by simp [IsOddSet, hv]
  obtain ⟨A, hA, hmin⟩ := exists_min_image
    (univ.filter fun A : Finset V => IsOddSet odd A) (cutCapacity c)
    ⟨{v}, by simp [hv']⟩
  exact ⟨A, (mem_filter.mp hA).2, fun U hU => hmin U (by simp [hU])⟩

private lemma min_odd_compl {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hs : ∀ i j, c i j = c j i)
    (odd A : Finset V) (he : Even odd.card) (hA : IsOddMinCut c odd A) :
    IsOddMinCut c odd Aᶜ := by
  refine ⟨odd_compl odd A he hA.1, ?_⟩
  intro U hU
  rw [cut_compl c hs A]
  exact hA.2 U hU

private lemma min_pair_compl {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hs : ∀ i j, c i j = c j i)
    (odd M : Finset V) (hM : IsMinOddPairCut c odd M) :
    IsMinOddPairCut c odd Mᶜ := by
  obtain ⟨p, hp, q, hq, hpM, hqM⟩ := hM.1
  refine ⟨⟨q, hq, p, hp, mem_compl.mpr hqM, ?_⟩, ?_⟩
  · simpa using hpM
  · intro U hU
    rw [cut_compl c hs M]
    exact hM.2 U hU

private lemma uncross_side {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (hs : ∀ i j, c i j = c j i) (hn : ∀ i j, 0 ≤ c i j)
    (odd M A : Finset V) (he : Even odd.card)
    (hM : IsMinOddPairCut c odd M) (hMe : Even (M ∩ odd).card)
    (hA : IsOddMinCut c odd A) (hAM : IsOddSet odd (A ∩ M)) :
    ∃ X : Finset V, IsOddMinCut c odd X ∧ X ⊆ M := by
  obtain ⟨p, hp, q, hq, hpM, hqM⟩ := hM.1
  have hAcM : IsOddSet odd (Aᶜ ∩ M) := by
    have h := card_partition A (M ∩ odd)
    simp only [← inter_assoc] at h
    unfold IsOddSet at hAM ⊢
    rw [Nat.even_iff] at hMe
    rw [Nat.odd_iff] at hAM ⊢
    omega
  have step (B : Finset V) (hB : IsOddMinCut c odd B)
      (hBM : IsOddSet odd (B ∩ M)) (hqB : q ∉ B) :
      IsOddMinCut c odd (B ∩ M) := by
    refine ⟨hBM, ?_⟩
    have hsep : SeparatesOddPair odd (B ∪ M) :=
      ⟨p, hp, q, hq, mem_union_right _ hpM, by simp [hqB, hqM]⟩
    have hlower := hM.2 (B ∪ M) hsep
    have hsub := cut_submodular c hn B M
    intro U hU
    have hBU := hB.2 U hU
    linarith
  by_cases hqA : q ∈ A
  · exact ⟨Aᶜ ∩ M, step Aᶜ (min_odd_compl c hs odd A he hA) hAcM
      (by simpa using hqA), inter_subset_right⟩
  · exact ⟨A ∩ M, step A hA hAM hqA, inter_subset_right⟩

/-- Padberg–Rao Lemma 1.1, by symmetric submodular uncrossing. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ)
    (hc_symm : ∀ i j, c i j = c j i) (hc_nonneg : ∀ i j, 0 ≤ c i j)
    (odd : Finset V) (hodd_ne : odd.Nonempty) (hodd_even : Even odd.card)
    (M : Finset V) (hM : IsMinOddPairCut c odd M) :
    ∃ X : Finset V, IsOddMinCut c odd X ∧ (X ⊆ M ∨ X ⊆ Mᶜ) := by
  classical
  by_cases hMo : IsOddSet odd M
  · exact ⟨M, ⟨hMo, fun U hU => hM.2 U (odd_sep odd U hodd_even hU)⟩,
      Or.inl Subset.rfl⟩
  have hMe : Even (M ∩ odd).card := by
    simpa only [IsOddSet, Nat.not_odd_iff_even] using hMo
  obtain ⟨A, hA⟩ := min_odd_exists c odd hodd_ne
  by_cases hAM : IsOddSet odd (A ∩ M)
  · obtain ⟨X, hX, hXM⟩ := uncross_side c hc_symm hc_nonneg odd M A
      hodd_even hM hMe hA hAM
    exact ⟨X, hX, Or.inl hXM⟩
  · have hAcM : IsOddSet odd (A ∩ Mᶜ) := by
      have h := card_partition M (A ∩ odd)
      have hAo := hA.1
      unfold IsOddSet at hAM hAo ⊢
      simp only [← inter_assoc, inter_comm M A, inter_comm Mᶜ A] at h
      rw [Nat.odd_iff] at hAM hAo ⊢
      omega
    have hMce : Even (Mᶜ ∩ odd).card := by
      have h := card_partition M odd
      rw [Nat.even_iff] at hMe hodd_even ⊢
      omega
    obtain ⟨X, hX, hXM⟩ := uncross_side c hc_symm hc_nonneg odd Mᶜ A
      hodd_even (min_pair_compl c hc_symm odd M hM) hMce hA hAcM
    exact ⟨X, hX, Or.inr hXM⟩

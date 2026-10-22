-- Prove2me | solution 1 for TheoryOfGames.ThreePerson.middlePointsSet_isSolution
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:03:16.237224+00:00
-- url     : https://prove2.me/submissions/6dc76390-af7f-43a6-beb3-2692513cfd70

import Mathlib
import Definitions.Def_TheoryOfGames_ThreePerson_Solution
import Definitions.Def_TheoryOfGames_ThreePerson_ReducedThreePerson

set_option autoImplicit false
open TheoryOfGames.ThreePerson

theorem dom_iff (α β : Fin 3 → ℝ) (hα : IsImputation redV α)
    (hβ : IsImputation redV β) :
    Dominates redV α β ↔
      (β 0 < α 0 ∧ β 1 < α 1) ∨ (β 0 < α 0 ∧ β 2 < α 2) ∨ (β 1 < α 1 ∧ β 2 < α 2) := by
  obtain ⟨hα1, hα2⟩ := hα
  obtain ⟨hβ1, hβ2⟩ := hβ
  have hv1 : ∀ i : Fin 3, redV {i} = -1 := fun i => by simp [redV]
  have hα1' : ∀ i, -1 ≤ α i := fun i => by simpa [hv1 i] using hα1 i
  have hβ1' : ∀ i, -1 ≤ β i := fun i => by simpa [hv1 i] using hβ1 i
  rw [Fin.sum_univ_three] at hα2 hβ2
  constructor
  · rintro ⟨S, hS, heff, hlt⟩
    by_cases hc : S.card = 1
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
      have h1 := heff
      simp only [IsEffective, Finset.sum_singleton, hv1] at h1
      have h2 := hlt i (Finset.mem_singleton_self i)
      have := hβ1' i
      linarith
    · have h2 : 1 < S.card := by
        have := hS.card_pos
        omega
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h2
      have hi' := hlt i hi
      have hj' := hlt j hj
      fin_cases i <;> fin_cases j <;> simp at hij <;> simp at hi' hj' <;> tauto
  · intro h
    have e2 : ∀ i j : Fin 3, i ≠ j → redV {i, j} = 1 := by
      intro i j hij
      simp [redV, Finset.card_pair hij]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨{0, 1}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 0 1 (by decide)]
        simp [Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide)]
        linarith [hα1' 2]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
    · refine ⟨{0, 2}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 0 2 (by decide)]
        simp [Finset.sum_pair (show (0 : Fin 3) ≠ 2 by decide)]
        linarith [hα1' 1]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
    · refine ⟨{1, 2}, by simp, ?_, ?_⟩
      · simp only [IsEffective]
        rw [e2 1 2 (by decide)]
        simp [Finset.sum_pair (show (1 : Fin 3) ≠ 2 by decide)]
        linarith [hα1' 0]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption

theorem imp_iff (α : Fin 3 → ℝ) :
    IsImputation redV α ↔ (∀ i, -1 ≤ α i) ∧ α 0 + α 1 + α 2 = 0 := by
  have hv1 : ∀ i : Fin 3, redV {i} = -1 := fun i => by simp [redV]
  unfold IsImputation
  rw [Fin.sum_univ_three]
  simp only [hv1]


theorem solution : IsSolution redV middlePointsSet := by
  have hmem : ∀ α ∈ middlePointsSet, IsImputation redV α := by
    intro α hα
    simp only [middlePointsSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hα
    rw [imp_iff]
    rcases hα with rfl | rfl | rfl <;>
      refine ⟨fun i => ?_, ?_⟩ <;> first | (fin_cases i <;> norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]) | norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  refine ⟨hmem, ?_, ?_⟩
  · intro α hα β hβ hdom
    rw [dom_iff α β (hmem α hα) (hmem β hβ)] at hdom
    simp only [middlePointsSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hα hβ
    rcases hα with rfl | rfl | rfl <;> rcases hβ with rfl | rfl | rfl <;> norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at hdom
  · intro β hβ hnot
    obtain ⟨hb, hsum⟩ := (imp_iff β).mp hβ
    have hb0 := hb 0
    have hb1 := hb 1
    have hb2 := hb 2
    have m1 : (![-1, 1 / 2, 1 / 2] : Fin 3 → ℝ) ∈ middlePointsSet := by simp [middlePointsSet]
    have m2 : (![1 / 2, -1, 1 / 2] : Fin 3 → ℝ) ∈ middlePointsSet := by simp [middlePointsSet]
    have m3 : (![1 / 2, 1 / 2, -1] : Fin 3 → ℝ) ∈ middlePointsSet := by simp [middlePointsSet]
    have i1 := hmem _ m1
    have i2 := hmem _ m2
    have i3 := hmem _ m3
    rcases lt_or_ge (β 0) (1 / 2) with h0 | h0 <;> rcases lt_or_ge (β 1) (1 / 2) with h1 | h1 <;>
      rcases lt_or_ge (β 2) (1 / 2) with h2 | h2
    · exact ⟨_, m1, (dom_iff _ β i1 hβ).mpr (Or.inr (Or.inr ⟨by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using h1, by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using h2⟩))⟩
    · exact ⟨_, m3, (dom_iff _ β i3 hβ).mpr (Or.inl ⟨by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using h0, by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using h1⟩)⟩
    · exact ⟨_, m2, (dom_iff _ β i2 hβ).mpr (Or.inr (Or.inl ⟨by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using h0, by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using h2⟩))⟩
    · exfalso; apply hnot
      simp only [middlePointsSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      left; funext i; fin_cases i <;> simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> linarith
    · exact ⟨_, m1, (dom_iff _ β i1 hβ).mpr (Or.inr (Or.inr ⟨by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using h1, by simpa [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] using h2⟩))⟩
    · exfalso; apply hnot
      simp only [middlePointsSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      right; left; funext i; fin_cases i <;> simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> linarith
    · exfalso; apply hnot
      simp only [middlePointsSet, Set.mem_insert_iff, Set.mem_singleton_iff]
      right; right; funext i; fin_cases i <;> simp [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> linarith
    · exfalso; linarith

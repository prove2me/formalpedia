-- Prove2me | solution 1 for RobustSpecClust.Est.eq_E2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T23:52:36.191929+00:00
-- url     : https://prove2.me/submissions/1aa136cd-acc4-488c-bd58-17e3c80923cd

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

namespace Aux_RSCE2

lemma swap3 {α β γ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ) (f : α → β → γ → ℝ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ b ∈ t, ∑ c ∈ u, ∑ a ∈ s, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

end Aux_RSCE2

open RobustSpecClust.Est Aux_RSCE2 in
theorem solution {n m r : ℕ} (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r) (τin : ℝ)
    (τout : Fin r → Fin r → ℝ) (γ : ℝ)
    (hK : ∀ i j, 0 ≤ inlierBlock K i j ∧ inlierBlock K i j ≤ 1)
    (hτin : 0 ≤ τin ∧ τin ≤ 1) (hτout : ∀ k l, k ≠ l → 0 ≤ τout k l ∧ τout k l ≤ 1) :
    l1 (inlierBlock K - inlierBlock (refMatrix K φ τin τout γ)) ≤
      ∑ i, ∑ j, (if φ i = φ j then (if K (Sum.inl i) (Sum.inl j) < τin then τin else 0)
        else (if τout (φ i) (φ j) < K (Sum.inl i) (Sum.inl j) then 1 - τout (φ i) (φ j) else 0)) ∧
    ∑ i, ∑ j, (if φ i = φ j then (if K (Sum.inl i) (Sum.inl j) < τin then τin else 0)
        else (if τout (φ i) (φ j) < K (Sum.inl i) (Sum.inl j) then 1 - τout (φ i) (φ j) else 0)) ≤
      ∑ k, (mcDiag K φ τin k : ℝ) + ∑ k, ∑ l ∈ Finset.univ.erase k, (mcOff K φ τout k l : ℝ) := by
  constructor
  · unfold l1
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have hk := hK i j
    simp only [inlierBlock] at hk
    simp only [Matrix.sub_apply, inlierBlock, refMatrix]
    split_ifs with h1 h2 h3
    · rw [max_eq_right h2.le, abs_of_nonpos (by linarith)]; linarith
    · rw [max_eq_left (not_lt.1 h2), sub_self, abs_zero]
    · rw [min_eq_right h3.le, abs_of_nonneg (by linarith)]; linarith
    · rw [min_eq_left (not_lt.1 h3), sub_self, abs_zero]
  · set D : Fin r → Fin n → Fin n → ℝ := fun k i j =>
      if φ i = k ∧ φ j = k ∧ K (Sum.inl i) (Sum.inl j) < τin then 1 else 0 with hDdef
    set O : Fin r → Fin r → Fin n → Fin n → ℝ := fun k l i j =>
      if φ i = k ∧ φ j = l ∧ τout k l < K (Sum.inl i) (Sum.inl j) then 1 else 0 with hOdef
    have hD : ∀ k, (mcDiag K φ τin k : ℝ) = ∑ i, ∑ j, D k i j := by
      intro k
      simp only [mcDiag, Finset.natCast_card_filter, Finset.sum_product, hDdef]
    have hO : ∀ k l, (mcOff K φ τout k l : ℝ) = ∑ i, ∑ j, O k l i j := by
      intro k l
      simp only [mcOff, Finset.natCast_card_filter, Finset.sum_product, hOdef]
    have hR : ∑ k, (mcDiag K φ τin k : ℝ) + ∑ k, ∑ l ∈ Finset.univ.erase k, (mcOff K φ τout k l : ℝ) =
        ∑ i, ∑ j, (∑ k, D k i j + ∑ k, ∑ l ∈ Finset.univ.erase k, O k l i j) := by
      simp only [hD, hO]
      rw [swap3]
      have : ∀ k, ∑ l ∈ Finset.univ.erase k, ∑ i, ∑ j, O k l i j =
          ∑ i, ∑ j, ∑ l ∈ Finset.univ.erase k, O k l i j := fun k => swap3 _ _ _ _
      simp only [this]
      rw [swap3 Finset.univ Finset.univ Finset.univ
        (fun k i j => ∑ l ∈ Finset.univ.erase k, O k l i j)]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_add_distrib]
    rw [hR]
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    have hDnn : ∀ k i j, 0 ≤ D k i j := by intro k i j; simp only [hDdef]; split_ifs <;> norm_num
    have hOnn : ∀ k l i j, 0 ≤ O k l i j := by
      intro k l i j; simp only [hOdef]; split_ifs <;> norm_num
    have hSD : 0 ≤ ∑ k, D k i j := Finset.sum_nonneg (fun k _ => hDnn k i j)
    have hSO : 0 ≤ ∑ k, ∑ l ∈ Finset.univ.erase k, O k l i j :=
      Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun l _ => hOnn k l i j))
    by_cases hφ : φ i = φ j
    · rw [if_pos hφ]
      have h1 : D (φ i) i j ≤ ∑ k, D k i j :=
        Finset.single_le_sum (fun k _ => hDnn k i j) (Finset.mem_univ _)
      by_cases hk : K (Sum.inl i) (Sum.inl j) < τin
      · rw [if_pos hk]
        have : D (φ i) i j = 1 := by simp [hDdef, hφ, hk]
        linarith [hτin.2]
      · rw [if_neg hk]; linarith
    · rw [if_neg hφ]
      have h1 : O (φ i) (φ j) i j ≤ ∑ l ∈ Finset.univ.erase (φ i), O (φ i) l i j :=
        Finset.single_le_sum (fun l _ => hOnn (φ i) l i j)
          (Finset.mem_erase.2 ⟨Ne.symm hφ, Finset.mem_univ _⟩)
      have h2 : ∑ l ∈ Finset.univ.erase (φ i), O (φ i) l i j ≤
          ∑ k, ∑ l ∈ Finset.univ.erase k, O k l i j :=
        Finset.single_le_sum (f := fun k => ∑ l ∈ Finset.univ.erase k, O k l i j)
          (fun k _ => Finset.sum_nonneg (fun l _ => hOnn k l i j)) (Finset.mem_univ _)
      by_cases hk : τout (φ i) (φ j) < K (Sum.inl i) (Sum.inl j)
      · rw [if_pos hk]
        have : O (φ i) (φ j) i j = 1 := by simp [hOdef, hk]
        have := (hτout (φ i) (φ j) hφ).1
        linarith
      · rw [if_neg hk]; linarith

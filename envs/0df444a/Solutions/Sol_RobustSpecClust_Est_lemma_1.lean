-- Prove2me | solution 1 for RobustSpecClust.Est.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:04:53.048779+00:00
-- url     : https://prove2.me/submissions/81493cea-4f71-42ca-a513-cdbf173d756c

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

open RobustSpecClust.Est in
theorem solution {n m r : ℕ} (K : Matrix (Pt n m) (Pt n m) ℝ) (φ : Fin n → Fin r) (τin : ℝ)
    (τout : Fin r → Fin r → ℝ) (γ : ℝ)
    (hin : ∀ i j, φ i = φ j → γ < refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j))
    (hout : ∀ i j, φ i ≠ φ j → refMatrix K φ τin τout γ (Sum.inl i) (Sum.inl j) < γ) :
    (∀ i j, 0 ≤ trueClust (m := m) φ i j ∧ trueClust (m := m) φ i j ≤ 1) ∧
    ∀ X : Matrix (Pt n m) (Pt n m) ℝ, (∀ i j, 0 ≤ X i j ∧ X i j ≤ 1) →
      frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) X ≤
        frobInner (refMatrix K φ τin τout γ - γ • ones (Pt n m)) (trueClust φ) := by
  constructor
  · intro i j
    rcases i with i | i <;> rcases j with j | j <;> simp only [trueClust] <;>
      (try split_ifs) <;> norm_num
  · intro X hX
    unfold frobInner
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨h0, h1⟩ := hX i j
    rcases i with i | i <;> rcases j with j | j
    · by_cases hij : φ i = φ j
      · have := hin i j hij
        simp only [Matrix.sub_apply, Matrix.smul_apply, ones, Matrix.of_apply, smul_eq_mul,
          mul_one, trueClust, if_pos hij]
        nlinarith
      · have := hout i j hij
        simp only [Matrix.sub_apply, Matrix.smul_apply, ones, Matrix.of_apply, smul_eq_mul,
          mul_one, trueClust, if_neg hij]
        nlinarith
    all_goals simp [refMatrix, trueClust, ones]

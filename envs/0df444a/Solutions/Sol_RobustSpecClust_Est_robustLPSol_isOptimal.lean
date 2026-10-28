-- Prove2me | solution 1 for RobustSpecClust.Est.robustLPSol_isOptimal
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:08:25.806125+00:00
-- url     : https://prove2.me/submissions/b6f441db-cd65-4c19-9477-785bce2a8278

import Mathlib
import Definitions.Def_RobustSpecClust_Est_Setting
open MeasureTheory ProbabilityTheory

open RobustSpecClust.Est in
theorem solution {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (γ : ℝ) :
    (∀ i j, 0 ≤ robustLPSol K γ i j ∧ robustLPSol K γ i j ≤ 1) ∧
    ∀ X : Matrix ι ι ℝ, (∀ i j, 0 ≤ X i j ∧ X i j ≤ 1) →
      frobInner (K - γ • ones ι) X ≤ frobInner (K - γ • ones ι) (robustLPSol K γ) := by
  refine ⟨fun i j => ?_, fun X hX => ?_⟩
  · unfold robustLPSol
    by_cases h : γ < K i j
    · rw [if_pos h]; exact ⟨zero_le_one, le_rfl⟩
    · rw [if_neg h]; exact ⟨le_rfl, zero_le_one⟩
  · unfold frobInner
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨h0, h1⟩ := hX i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, ones, Matrix.of_apply, smul_eq_mul,
      mul_one, robustLPSol]
    by_cases h : γ < K i j
    · rw [if_pos h]; nlinarith
    · rw [if_neg h]; nlinarith

-- Prove2me | solution 1 for QueueingFundamentals.Numerical.uniformized_matrix_stochastic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:33:33.242983+00:00
-- url     : https://prove2.me/submissions/8866427a-7dd0-4d94-80cb-c7a402be6e63

import Mathlib
import Definitions.Def_QueueingFundamentals_Numerical_Uniformization

open Matrix

open QueueingFundamentals.Numerical in
theorem solution {N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hQ : IsGenerator Q) (Λ : ℝ) (hΛ : 0 < Λ) (hΛq : ∀ i, exitRate Q i ≤ Λ) :
    (∀ i n, uniformizedMatrix Λ Q i n =
        if i ≠ n then Q i n / Λ else 1 - exitRate Q i / Λ) ∧
      IsStochastic (uniformizedMatrix Λ Q) := by
  have hent : ∀ i n, uniformizedMatrix Λ Q i n =
      if i ≠ n then Q i n / Λ else 1 - exitRate Q i / Λ := by
    intro i n
    unfold uniformizedMatrix exitRate
    by_cases h : i = n
    · subst h
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
        ne_eq, not_true_eq_false, if_false]
      field_simp
      ring
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_ne h,
        ne_eq, h, not_false_eq_true, if_true]
      field_simp
      ring
  refine ⟨hent, ?_, ?_⟩
  · intro i j
    rw [hent]
    by_cases h : i = j
    · subst h
      simp only [ne_eq, not_true_eq_false, if_false, sub_nonneg]
      rw [div_le_one hΛ]
      exact hΛq i
    · simp only [ne_eq, h, not_false_eq_true, if_true]
      exact div_nonneg (hQ.1 i j h) hΛ.le
  · intro i
    have hrow : ∑ j, Q i j = 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hQ.2 i]
      ring
    unfold uniformizedMatrix
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hrow, mul_zero, zero_add]
    simp [Matrix.one_apply]

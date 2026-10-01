-- Prove2me | solution 1 for burau_sl2_descent_word
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-10-01T06:09:22.830278+00:00
-- url     : https://prove2.me/submissions/1b30b01d-e624-459d-8e64-7b4a42313b5f

import Definitions.Def_burau_descent_word

set_option autoImplicit false

open Matrix

namespace BurauDescent

lemma Sm_mul_Sinv : Sm * Sinv = 1 := by decide

lemma Sm_mul_Sinv_mul (X : M2) : Sm * (Sinv * X) = X := by
  rw [← mul_assoc, Sm_mul_Sinv, one_mul]

lemma Tm_det (n : ℤ) : (Tm n).det = 1 := by simp [Tm, Matrix.det_fin_two]

lemma Sm_det : Sm.det = 1 := by simp [Sm, Matrix.det_fin_two]

lemma Tm_mul_apply00 (M : M2) (n : ℤ) : (M * Tm n) 0 0 = M 0 0 := by
  simp [Tm, Matrix.mul_apply, Fin.sum_univ_two]

lemma Tm_mul_apply01 (M : M2) (n : ℤ) : (M * Tm n) 0 1 = M 0 1 + M 0 0 * n := by
  simp [Tm, Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma Sm_mul_apply00 (M : M2) : (M * Sm) 0 0 = M 0 1 := by
  simp [Sm, Matrix.mul_apply, Fin.sum_univ_two]

lemma Tm_Tm (a b : ℤ) : Tm a * Tm b = Tm (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma Tm_zero : Tm 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tm, Matrix.one_fin_two]

/-- The Euclidean descent step: its `(0,0)`-entry is `M 0 1 % M 0 0`, so the measure drops. -/
lemma euclid_decrease_ (M : M2) (h : M 0 0 ≠ 0) :
    (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs < (M 0 0).natAbs := by
  have hkey : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0) = M 0 1 % M 0 0 := by
    rw [Sm_mul_apply00, Tm_mul_apply01]
    have h1 : M 0 1 + M 0 0 * (-(M 0 1 / M 0 0)) = M 0 1 % M 0 0 := by
      have hh := Int.mul_ediv_add_emod (M 0 1) (M 0 0)
      linear_combination -hh
    exact h1
  rw [hkey]
  have h1 : 0 ≤ M 0 1 % M 0 0 := Int.emod_nonneg _ h
  have h2 : M 0 1 % M 0 0 < |M 0 0| := Int.emod_lt_abs _ h
  have h4 : |M 0 1 % M 0 0| < |M 0 0| := by rwa [abs_of_nonneg h1]
  rw [Int.natAbs_lt_iff_sq_lt]
  exact sq_lt_sq.mpr h4

/-- Terminal case of the descent word: if `M 0 0 = 0` and `det M = 1` then `baseWord M` multiplies
back to `M`. -/
lemma baseWord_prod (M : M2) (hd : M.det = 1) (h0 : M 0 0 = 0) : (baseWord M).prod = M := by
  have hdet : M 0 1 * M 1 0 = -1 := by
    have h2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hd
    rw [h0] at h2
    simp only [zero_mul, zero_sub] at h2
    linarith
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp (by rw [mul_neg, hdet]; ring : M 0 1 * (-(M 1 0)) = 1) with
    ⟨h1, h10⟩ | ⟨h1, h10⟩
  · -- M 0 1 = 1, M 1 0 = -1  (the `else` branch of `baseWord`)
    have h10' : M 1 0 = -1 := by linarith [h10]
    have h1' : ¬ (M 0 1 = -1) := by rw [h1]; norm_num
    unfold baseWord
    rw [if_neg h1']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Sm, Tm, Matrix.mul_apply, Fin.sum_univ_two, h0, h1, h10'] <;> ring
  · -- M 0 1 = -1, M 1 0 = 1  (the `then` branch)
    have h10' : M 1 0 = 1 := by linarith [h10]
    unfold baseWord
    rw [if_pos h1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Sm, Tm, Matrix.mul_apply, Fin.sum_univ_two, h0, h1, h10'] <;> ring

/-- Main lemma: with a step budget at least `|M 0 0|`, the descent word multiplies back to `M`. -/
theorem iterWord_prod : ∀ k : ℕ, ∀ M : M2, M.det = 1 → (M 0 0).natAbs ≤ k →
    (iterWord k M).prod = M := by
  intro k
  induction k with
  | zero =>
      intro M hd hle
      have h0 : M 0 0 = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
      simpa [iterWord] using baseWord_prod M hd h0
  | succ k ih =>
      intro M hd hle
      by_cases h0 : M 0 0 = 0
      · simpa [iterWord, h0] using baseWord_prod M hd h0
      · have hlt : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs ≤ k := by
          have := euclid_decrease_ M h0
          omega
        have hd' : (((M * Tm (-(M 0 1 / M 0 0))) * Sm)).det = 1 := by
          rw [Matrix.det_mul, Matrix.det_mul, hd, Tm_det, Sm_det, mul_one, mul_one]
        have hIH := ih ((M * Tm (-(M 0 1 / M 0 0))) * Sm) hd' hlt
        have hT : Tm (-(M 0 1 / M 0 0)) * Tm (M 0 1 / M 0 0) = 1 := by
          rw [Tm_Tm]
          have : -(M 0 1 / M 0 0) + M 0 1 / M 0 0 = 0 := by ring
          rw [this, Tm_zero]
        simp only [iterWord, if_neg h0, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
        rw [hIH]
        simp only [mul_assoc]
        rw [Sm_mul_Sinv_mul, hT, mul_one]

end BurauDescent

theorem solution (M : BurauDescent.M2) (hd : M.det = 1) :
    (BurauDescent.word M).prod = M :=
  BurauDescent.iterWord_prod (M 0 0).natAbs M hd le_rfl

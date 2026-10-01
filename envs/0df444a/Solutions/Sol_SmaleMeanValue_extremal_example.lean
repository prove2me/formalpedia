-- Prove2me | solution 1 for SmaleMeanValue.extremal_example
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:22:04.711627+00:00
-- url     : https://prove2.me/submissions/e710709a-8dfd-4d65-869a-cca7f405f0b7

import Mathlib
open Polynomial

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (X ^ d - C (d : ℂ) * X : ℂ[X]).natDegree = d ∧
    (X ^ d - C (d : ℂ) * X : ℂ[X]).derivative.eval 0 ≠ 0 ∧
    ∀ c : ℂ, (X ^ d - C (d : ℂ) * X : ℂ[X]).derivative.eval c = 0 →
      ‖((X ^ d - C (d : ℂ) * X : ℂ[X]).eval 0 - (X ^ d - C (d : ℂ) * X : ℂ[X]).eval c)
          / (0 - c)‖
        = (((d : ℝ) - 1) / d) * ‖(X ^ d - C (d : ℂ) * X : ℂ[X]).derivative.eval 0‖ := by
  have hd0 : d ≠ 0 := by omega
  have hdm1 : d - 1 ≠ 0 := by omega
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hderiv (z : ℂ) :
      (X ^ d - C (d : ℂ) * X : ℂ[X]).derivative.eval z =
        (d : ℂ) * z ^ (d - 1) - d := by
    simp [derivative_X_pow, derivative_sub, derivative_mul]
  have hzero : (X ^ d - C (d : ℂ) * X : ℂ[X]).derivative.eval 0 = -(d : ℂ) := by
    rw [hderiv]
    simp [hdm1]
  refine ⟨?_, ?_, ?_⟩
  · rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    simp only [natDegree_C_mul_X _ hdC, natDegree_X_pow]
    omega
  · rw [hzero]
    exact neg_ne_zero.mpr hdC
  · intro c hc
    have hc0 : c ≠ 0 := by
      intro h
      subst c
      rw [hzero] at hc
      exact hdC (neg_eq_zero.mp hc)
    have hcpow : c ^ (d - 1) = 1 := by
      rw [hderiv] at hc
      apply mul_left_cancel₀ hdC
      simpa only [mul_one] using sub_eq_zero.mp hc
    have hcd : c ^ d = c := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ d by omega)]
      rw [pow_add, hcpow, pow_one, one_mul]
    have hquot :
        ((X ^ d - C (d : ℂ) * X : ℂ[X]).eval 0 -
          (X ^ d - C (d : ℂ) * X : ℂ[X]).eval c) / (0 - c) = 1 - (d : ℂ) := by
      simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, zero_pow hd0,
        mul_zero, sub_zero, zero_sub, hcd]
      field_simp
    rw [hquot, hzero, norm_neg]
    have hnorm : ‖(d : ℂ)‖ = (d : ℝ) := by simp
    rw [hnorm, div_mul_cancel₀ _ hdR]
    have hcast : (1 : ℂ) - d = ((1 - (d : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
    · ring
    · have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith

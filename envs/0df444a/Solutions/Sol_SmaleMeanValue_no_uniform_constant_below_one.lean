-- Prove2me | solution 1 for SmaleMeanValue.no_uniform_constant_below_one
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:22:15.601489+00:00
-- url     : https://prove2.me/submissions/c089d7aa-a7f3-41e9-929d-dbcd7848749b

import Mathlib
open Polynomial

theorem ImpactSmale.extremal_family (d : ℕ) (hd : 2 ≤ d) :
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


theorem solution (K : ℝ) (hK : K < 1) :
    ∃ P : ℂ[X], 2 ≤ P.natDegree ∧ ∃ z : ℂ, P.derivative.eval z ≠ 0 ∧
      ∀ c : ℂ, P.derivative.eval c = 0 →
        K * ‖P.derivative.eval z‖ < ‖(P.eval z - P.eval c) / (z - c)‖ := by
  have hgap : 0 < 1 - K := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - K))
  let d := n + 2
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hbound : K < ((d : ℝ) - 1) / d := by
    apply (lt_div_iff₀ hdpos).mpr
    have hn' : 1 < (n : ℝ) * (1 - K) := (div_lt_iff₀ hgap).mp hn
    have hdcast : (d : ℝ) = (n : ℝ) + 2 := by simp [d]
    rw [hdcast]
    nlinarith
  obtain ⟨hdegree, hzero, hequality⟩ := ImpactSmale.extremal_family d hd
  refine ⟨X ^ d - C (d : ℂ) * X, ?_, 0, hzero, ?_⟩
  · simpa only [hdegree] using hd
  · intro c hc
    rw [hequality c hc]
    exact mul_lt_mul_of_pos_right hbound (norm_pos_iff.mpr hzero)

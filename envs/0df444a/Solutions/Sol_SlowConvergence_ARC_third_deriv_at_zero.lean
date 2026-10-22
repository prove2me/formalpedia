-- Prove2me | solution 1 for SlowConvergence.ARC.third_deriv_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:23:41.713671+00:00
-- url     : https://prove2.me/submissions/3d8f5323-a3b1-4a39-8d81-282b134243bc

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

set_option autoImplicit false
open SlowConvergence.ARC

lemma poly5_deriv (c0 c1 c2 c3 c4 c5 : ℝ) :
    deriv (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 + c5 * t ^ 5) =
      fun t => c1 + (2 * c2) * t + (3 * c3) * t ^ 2 + (4 * c4) * t ^ 3 + (5 * c5) * t ^ 4
        + 0 * t ^ 5 := by
  funext t
  rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_add (by fun_prop) (by fun_prop),
    deriv_fun_add (by fun_prop) (by fun_prop)]
  simp
  ring

lemma poly5_third (c0 c1 c2 c3 c4 c5 : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4 + c5 * t ^ 5) 0
      = 6 * c3 := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
    poly5_deriv, poly5_deriv, poly5_deriv]
  simp
  ring

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    |iteratedDeriv 3 (p τ k) 0| ≤ 20 := by
  have hη : 0 < eta τ := by
    unfold eta
    have h : 2 / 3 < 2 / (3 - 2 * τ) := by
      rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  have hμ : 0 < mu τ := by unfold mu; linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hphi : phi τ k = 1 - (((k : ℝ) + 1) * (1 / ((k : ℝ) + 2))) ^ mu τ := by
    unfold phi
    rw [mul_sub, ← Real.mul_rpow hk1.le (by positivity), ← Real.mul_rpow hk1.le (by positivity)]
    have : ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) = 1 := by field_simp
    rw [this, Real.one_rpow]
  have hr0 : 0 < ((k : ℝ) + 1) * (1 / ((k : ℝ) + 2)) := by positivity
  have hr1 : ((k : ℝ) + 1) * (1 / ((k : ℝ) + 2)) < 1 := by
    rw [mul_one_div, div_lt_one hk2]; linarith
  have h1 := Real.rpow_lt_one hr0.le hr1 hμ
  have h2 := Real.rpow_pos_of_pos hr0 (mu τ)
  have hφ0 : 0 < phi τ k := by rw [hphi]; linarith
  have hφ1 : phi τ k < 1 := by rw [hphi]; linarith
  have key : iteratedDeriv 3 (p τ k) 0 = 6 * (10 / 3 - 4 * phi τ k) := by
    have := poly5_third (coeff τ k 0) (coeff τ k 1) (coeff τ k 2) (coeff τ k 3) (coeff τ k 4)
      (coeff τ k 5)
    unfold p
    rw [this]
    simp [coeff]
  rw [key, abs_le]
  constructor <;> linarith

-- Prove2me | solution 1 for RegevLWE.PeriodicGauss.final_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:55:35.723064+00:00
-- url     : https://prove2.me/submissions/ab534270-5224-4a87-a190-1b79c4120ddf

import Mathlib

set_option autoImplicit false
open MeasureTheory

lemma RLP_gauss2 (b : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = b ^ (-(3 : ℝ) / 2) * (Real.sqrt Real.pi / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := b) two_pos (by norm_num) hb
  simp_rw [Real.rpow_two] at h
  have hG : Real.Gamma ((2 + 1) / 2) = Real.sqrt Real.pi / 2 := by
    have : ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 := by norm_num
    rw [this, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have e : ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) =
      ∫ x : ℝ, (fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2)) |x| := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [sq_abs]
  have hca := integral_comp_abs (f := fun t : ℝ => t ^ 2 * Real.exp (-b * t ^ 2))
  rw [e, hca, h, hG]
  have : -((2 : ℝ) + 1) / 2 = -(3 : ℝ) / 2 := by norm_num
  rw [this]
  ring

theorem solution (ϵ : ℝ) (hϵ : 0 < ϵ) (hϵ1 : ϵ ≤ 1) :
    ϵ + 2 * Real.pi * ϵ * ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / (1 + ϵ) ^ 2) =
        ϵ + ϵ * (1 + ϵ) ^ 3 ∧
      ϵ + ϵ * (1 + ϵ) ^ 3 ≤ 9 * ϵ := by
  refine ⟨?_, by nlinarith [mul_pos hϵ hϵ, mul_pos (mul_pos hϵ hϵ) hϵ]⟩
  have hs : 0 < 1 + ϵ := by linarith
  have hpi := Real.pi_pos
  set s := 1 + ϵ with hsdef
  have hb : 0 < Real.pi / s ^ 2 := by positivity
  have hint : ∫ x : ℝ, x ^ 2 * Real.exp (-Real.pi * x ^ 2 / s ^ 2) =
      ∫ x : ℝ, x ^ 2 * Real.exp (-(Real.pi / s ^ 2) * x ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    congr 2
    ring
  rw [hint, RLP_gauss2 _ hb]
  -- b^(-3/2) = s^3 / π^(3/2)
  have hc : (Real.pi / s ^ 2) ^ (-(3 : ℝ) / 2) = s ^ 3 / (Real.sqrt Real.pi) ^ 3 := by
    have h1 : Real.pi / s ^ 2 = (Real.sqrt Real.pi / s) ^ (2 : ℕ) := by
      rw [div_pow, Real.sq_sqrt hpi.le]
    have hc0 : 0 < Real.sqrt Real.pi / s := by positivity
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    have : ((2 : ℕ) : ℝ) * (-(3 : ℝ) / 2) = -((3 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_neg hc0.le, Real.rpow_natCast, div_pow, inv_div]
  rw [hc]
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt hpi.le
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 hpi
  have h3 : Real.sqrt Real.pi ^ 3 = Real.pi * Real.sqrt Real.pi := by
    rw [pow_succ, hsq]
  have h4 : s ^ 3 / Real.sqrt Real.pi ^ 3 * (Real.sqrt Real.pi / 2) = s ^ 3 / (2 * Real.pi) := by
    rw [h3]; field_simp
  rw [h4]
  field_simp

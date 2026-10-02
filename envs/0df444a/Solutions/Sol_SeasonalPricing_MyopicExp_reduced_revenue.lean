-- Prove2me | solution 1 for SeasonalPricing.MyopicExp.reduced_revenue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:56:42.106617+00:00
-- url     : https://prove2.me/submissions/481f7bdc-714f-4bb0-a273-6fbf28d1fc9f

import Mathlib
import Definitions.Def_SeasonalPricing_MyopicExp_gammaValuationTail
import Definitions.Def_SeasonalPricing_Shared_LambdaI
import Definitions.Def_SeasonalPricing_MyopicExp_contingentMyopicRevenue

set_option autoImplicit false

open SeasonalPricing.MyopicExp SeasonalPricing.Shared in
theorem solution (lam α T p1 p2 : ℝ) (hlam : 0 < lam) (hT0 : 0 < T) (hT1 : T ≤ 1)
    (hα : 0 ≤ α) (hρ : decayRatio α 1 = 1) (hp2 : 0 ≤ p2) (hp21 : p2 ≤ p1) :
    contingentMyopicRevenue lam α T 1 (gammaValuationTail 1 1) p1 p2 =
      p2 * lam * Real.exp (-p2) + (p1 - p2) * lam * T * Real.exp (-p1) := by
  have hα0 : α = 0 := by
    unfold decayRatio at hρ
    have h := (Real.exp_eq_one_iff _).mp hρ
    linarith [mul_one α]
  subst hα0
  have hF : ∀ x : ℝ, gammaValuationTail 1 1 x = if 0 ≤ x then Real.exp (-x) else 1 := by
    intro x
    have h := ProbabilityTheory.cdf_expMeasure_eq (r := 1) one_pos x
    unfold ProbabilityTheory.expMeasure at h
    unfold gammaValuationTail
    simp only [one_pow, div_one, mul_one, one_mul] at h ⊢
    rw [h]
    split_ifs <;> ring
  have hFpos : ∀ x : ℝ, 0 ≤ x → gammaValuationTail 1 1 x = Real.exp (-x) := by
    intro x hx; rw [hF, if_pos hx]
  have hp1 : 0 ≤ p1 := le_trans hp2 hp21
  simp only [contingentMyopicRevenue, LambdaI, LambdaW, LambdaL, zero_mul, Real.exp_zero,
    mul_one, min_eq_right hp21, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  rw [hFpos p1 hp1, hFpos p2 hp2]
  ring

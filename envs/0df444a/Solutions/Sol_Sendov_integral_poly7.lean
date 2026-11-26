-- Prove2me | solution 1 for Sendov.integral_poly7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:05.137223+00:00
-- url     : https://prove2.me/submissions/5b6a4ada-ad9b-4d0d-a9f0-61fabc2176c5

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Theorems.Thm_Sendov_intervalIntegrable_const_mul_pow

set_option autoImplicit false
open Sendov
open MeasureTheory Finset
namespace Sendov
theorem _root_.solution (a₀ a₁ a₂ a₃ a₄ : ℝ) :
    (∫ t in (0 : ℝ)..1, (a₀ * t ^ 3 + a₁ * t ^ 4 + a₂ * t ^ 5 + a₃ * t ^ 6 + a₄ * t ^ 7))
      = a₀ / 4 + a₁ / 5 + a₂ / 6 + a₃ / 7 + a₄ / 8 := by
  have h₀ := intervalIntegrable_const_mul_pow a₀ 3
  have h₁ := intervalIntegrable_const_mul_pow a₁ 4
  have h₂ := intervalIntegrable_const_mul_pow a₂ 5
  have h₃ := intervalIntegrable_const_mul_pow a₃ 6
  have h₄ := intervalIntegrable_const_mul_pow a₄ 7
  rw [intervalIntegral.integral_add (((h₀.add h₁).add h₂).add h₃) h₄,
    intervalIntegral.integral_add ((h₀.add h₁).add h₂) h₃,
    intervalIntegral.integral_add (h₀.add h₁) h₂,
    intervalIntegral.integral_add h₀ h₁,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow, integral_pow, integral_pow, integral_pow, integral_pow]
  norm_num
  ring
end Sendov

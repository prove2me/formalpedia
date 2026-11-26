-- Prove2me | solution 1 for Sendov.integral_QQ_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:44:45.20981+00:00
-- url     : https://prove2.me/submissions/a0f06926-3663-4fa8-a9a0-07382e3bbdcd

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
import Theorems.Thm_Sendov_QQ_nonneg
import Theorems.Thm_Sendov_continuous_pow_mul_QQ


set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {c₁ c₂ A : ℝ} (hle : c₁ ≤ c₂) (hfeas : c₂ ^ 2 ≤ A) {r : ℝ} (hr : 0 ≤ r)
    (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c₂ A t ^ r)
      ≤ ∫ t in (0 : ℝ)..1, t ^ k * QQ c₁ A t ^ r := by
  refine intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_pow_mul_QQ c₂ A k hr).intervalIntegrable _ _)
    ((continuous_pow_mul_QQ c₁ A k hr).intervalIntegrable _ _) ?_
  intro u hu
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hu.1 k)
  refine Real.rpow_le_rpow (QQ_nonneg hfeas u) ?_ hr
  simp only [QQ]
  nlinarith [hu.1, hle]
end Sendov

-- Prove2me | solution 1 for TruncExpDensity.integral_truncExp_affine_Ioc_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T06:09:09.286297+00:00
-- url     : https://prove2.me/submissions/9ed52e6e-c3e8-4352-8d36-6d9c0db3d7e1

import Mathlib
import Theorems.Thm_TruncExpDensity_integral_exp_affine
import Theorems.Thm_TruncExpDensity_integral_truncExp_mul

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

-- carved from submission 510cef8c-8e14-4ee8-8b48-e4ca3a7e7938, lines 1727-1735

theorem solution (μ δ k : ℝ) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hδ1 : δ ≤ 1) (u v : ℝ) :
    (∫ t in μ..1,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*(u*t+v))=
      if μ ≤ δ then k*(Real.exp δ*(u*δ+v-u)-Real.exp μ*(u*μ+v-u)) else 0 := by
  rw [intervalIntegral.integral_of_le hμ1,TruncExpDensity.integral_truncExp_mul μ 1 δ k hμ hμ1,min_eq_right hδ1]
  by_cases h : μ ≤ δ
  · rw [if_pos h,TruncExpDensity.integral_exp_affine μ δ k u v h]
  · rw [if_neg h,Set.Ioc_eq_empty_of_le (le_of_not_ge h)]
    simp

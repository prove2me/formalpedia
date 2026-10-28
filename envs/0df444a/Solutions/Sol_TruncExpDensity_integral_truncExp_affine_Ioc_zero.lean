-- Prove2me | solution 1 for TruncExpDensity.integral_truncExp_affine_Ioc_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T06:09:08.771171+00:00
-- url     : https://prove2.me/submissions/1148cf11-0629-4d18-8b9a-f0f5ed583fc2

import Mathlib
import Theorems.Thm_TruncExpDensity_integral_exp_affine
import Theorems.Thm_TruncExpDensity_integral_truncExp_mul

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

-- carved from submission 510cef8c-8e14-4ee8-8b48-e4ca3a7e7938, lines 1721-1726

theorem solution (η δ k : ℝ) (hη : 0 ≤ η) (hδ : 0 ≤ δ) (u v : ℝ) :
    (∫ t in (0 : ℝ)..η,(if 0 < t ∧ t ≤ δ then k*Real.exp t else 0)*(u*t+v))=
      k*(Real.exp (min η δ)*(u*min η δ+v-u)-(v-u)) := by
  rw [intervalIntegral.integral_of_le hη,TruncExpDensity.integral_truncExp_mul 0 η δ k le_rfl hη]
  rw [TruncExpDensity.integral_exp_affine 0 (min η δ) k u v (le_min hη hδ)]
  simp

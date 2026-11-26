-- Prove2me | solution 1 for Sendov.norm_le_lowX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:05:25.999796+00:00
-- url     : https://prove2.me/submissions/e34390c0-9ada-4e7c-ba02-d700960ba543

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht0 : 0 ≤ t) {v : ℂ}
    (hv : ‖v‖ ≤ 1) : ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖ ≤ lowX a t := by
  have hb : (0 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  have hcast : (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v
      = ((a : ℝ) : ℂ) + ((t * (1 - a ^ 2) : ℝ) : ℂ) * v := by push_cast; ring
  rw [hcast]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha0, abs_of_nonneg (mul_nonneg ht0 hb)]
  simp only [lowX]
  nlinarith [hv, norm_nonneg v, mul_nonneg ht0 hb]
end Sendov

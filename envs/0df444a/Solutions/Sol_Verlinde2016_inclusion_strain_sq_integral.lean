-- Prove2me | solution 1 for Verlinde2016.inclusion_strain_sq_integral
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:53:05.327983+00:00
-- url     : https://prove2.me/submissions/8afe2f02-ea23-4475-8c2a-943dba50f557

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic
set_option autoImplicit false
open Real MeasureTheory

theorem solution (c : ℝ) (hc : 0 < c) :
    ∫ V in Set.Ioi c, (c / V) ^ 2 = c := by
  have he : (fun V : ℝ => (c/V)^2) = (fun V => c^2 * V^(-2:ℝ)) := by
    funext V
    simp [Real.rpow_neg, Real.rpow_two, div_pow, div_eq_mul_inv, mul_pow, inv_pow]
  rw [he, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hc]
  norm_num [Real.rpow_neg_one]
  field_simp

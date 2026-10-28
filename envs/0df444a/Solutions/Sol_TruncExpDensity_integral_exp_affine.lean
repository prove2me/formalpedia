-- Prove2me | solution 1 for TruncExpDensity.integral_exp_affine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T06:07:46.487585+00:00
-- url     : https://prove2.me/submissions/465209bd-0892-4ffc-82af-faa644521f4a

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open Set MeasureTheory

-- carved from submission 510cef8c-8e14-4ee8-8b48-e4ca3a7e7938, lines 1688-1701

theorem solution (a b k u v : ℝ) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b,k*Real.exp t*(u*t+v))=
      k*(Real.exp b*(u*b+v-u)-Real.exp a*(u*a+v-u)) := by
  rw [← intervalIntegral.integral_of_le hab]
  have hd (t : ℝ) : HasDerivAt (fun t => k*(Real.exp t*(u*t+v-u))) (k*Real.exp t*(u*t+v)) t := by
    convert! (((Real.hasDerivAt_exp t).mul (((hasDerivAt_id t).const_mul u).add_const (v-u))).const_mul k) using 1
    · ext x
      simp only [Pi.mul_apply,id_eq]
      ring
    · simp only [id_eq]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) ((show Continuous (fun t : ℝ => k*Real.exp t*(u*t+v)) by fun_prop).intervalIntegrable a b)]
  ring

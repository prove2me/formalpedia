-- Prove2me | solution 1 for Sendov.norm_sq_add_real_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:03:13.323741+00:00
-- url     : https://prove2.me/submissions/cb0c5cbe-ed8f-45f8-a093-46c225ff6cd2

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution (a s : ℝ) (v : ℂ) :
    ‖(a : ℂ) + (s : ℂ) * v‖ ^ 2 = a ^ 2 + 2 * a * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
end Sendov

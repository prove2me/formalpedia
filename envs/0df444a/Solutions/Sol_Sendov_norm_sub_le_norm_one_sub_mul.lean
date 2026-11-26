-- Prove2me | solution 1 for Sendov.norm_sub_le_norm_one_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:57.048752+00:00
-- url     : https://prove2.me/submissions/677e0b19-1e66-4569-8486-09474d03b8d8

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
theorem _root_.solution {a : ℝ} (ha : |a| ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(a : ℂ) - z‖ ≤ ‖1 - (a : ℂ) * z‖ := by
  have hkey : Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z)
      = (1 - a ^ 2) * (1 - Complex.normSq z) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have ha2 : a ^ 2 ≤ 1 := by
    have := abs_le.1 ha
    nlinarith [this.1, this.2]
  have hz2 : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  have hdiff : 0 ≤ Complex.normSq (1 - (a : ℂ) * z) - Complex.normSq ((a : ℂ) - z) := by
    rw [hkey]
    have h1 : (0 : ℝ) ≤ 1 - a ^ 2 := by linarith
    have h2 : (0 : ℝ) ≤ 1 - Complex.normSq z := by linarith
    positivity
  have hsq : ‖(a : ℂ) - z‖ ^ 2 ≤ ‖1 - (a : ℂ) * z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  nlinarith [norm_nonneg ((a : ℂ) - z), norm_nonneg (1 - (a : ℂ) * z), hsq]
end Sendov

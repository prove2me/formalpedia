-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshInh.le_avg_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:15.82838+00:00
-- url     : https://prove2.me/submissions/60ed43f9-6a98-4481-9155-0eaad2544f95

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshInh_ci_of_cont
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshInh_avg_re_affine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshInh
open MeasureTheory Metric Set Filter Topology Real
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshInh
theorem _root_.solution (a b : ℂ) : ‖a‖ ^ 2 ≤ Real.circleAverage (fun ζ : ℂ => ‖a + ζ * b‖ ^ 2) 0 1 := by
  have key : ∀ x : ℂ, (2 * (starRingEnd ℂ) a * x).re - ‖a‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    have := sq_nonneg (x.re - a.re)
    have := sq_nonneg (x.im - a.im)
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  have hE : Real.circleAverage (fun ζ : ℂ => (2 * (starRingEnd ℂ) a * (a + ζ * b)).re - ‖a‖ ^ 2)
      0 1 = ‖a‖ ^ 2 := by
    rw [Real.circleAverage_fun_sub (ci_of_cont (by fun_prop)) (ci_of_cont (by fun_prop)),
      avg_re_affine, Real.circleAverage_const]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [← hE]
  exact Real.circleAverage_mono (ci_of_cont (by fun_prop)) (ci_of_cont (by fun_prop))
    fun x _ => key _
end ReciprocityTheory.AnForm.A.PshInh

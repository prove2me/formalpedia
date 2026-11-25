-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshInh.le_avg_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:10.871682+00:00
-- url     : https://prove2.me/submissions/7156b0fb-3a69-454d-9c8d-03c563d1f4c6

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
theorem _root_.solution (a b : ℂ) : ‖a‖ ≤ Real.circleAverage (fun ζ : ℂ => ‖a + ζ * b‖) 0 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [norm_zero]
    exact Real.circleAverage_nonneg_of_nonneg fun _ _ => norm_nonneg _
  have h1 : ‖a‖ ^ 2 = Real.circleAverage
      (fun ζ : ℂ => ((starRingEnd ℂ) a * (a + ζ * b)).re) 0 1 := by
    rw [avg_re_affine, Complex.conj_mul']
    norm_cast
  have h2 : Real.circleAverage (fun ζ : ℂ => ((starRingEnd ℂ) a * (a + ζ * b)).re) 0 1 ≤
      Real.circleAverage (fun ζ : ℂ => ‖a‖ * ‖a + ζ * b‖) 0 1 := by
    refine Real.circleAverage_mono (ci_of_cont (by fun_prop)) (ci_of_cont (by fun_prop))
      fun x _ => (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h3 : Real.circleAverage (fun ζ : ℂ => ‖a‖ * ‖a + ζ * b‖) 0 1 =
      ‖a‖ * Real.circleAverage (fun ζ : ℂ => ‖a + ζ * b‖) 0 1 := by
    simpa [smul_eq_mul] using
      Real.circleAverage_fun_smul (a := ‖a‖) (f := fun ζ : ℂ => ‖a + ζ * b‖) (c := 0) (R := 1)
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  refine le_of_mul_le_mul_left ?_ hpos
  nlinarith
end ReciprocityTheory.AnForm.A.PshInh

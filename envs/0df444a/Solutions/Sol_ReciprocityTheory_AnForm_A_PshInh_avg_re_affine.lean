-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshInh.avg_re_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:38.851097+00:00
-- url     : https://prove2.me/submissions/7051ed38-e158-4f38-ba84-bcfe89b6ae58

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshInh_avg_affine

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
theorem _root_.solution (a b c : ℂ) :
    Real.circleAverage (fun ζ : ℂ => (c * (a + ζ * b)).re) 0 1 = (c * a).re := by
  have hi : CircleIntegrable (fun ζ : ℂ => a + ζ * b) 0 1 :=
    ((by fun_prop : Continuous (fun ζ : ℂ => a + ζ * b)).comp
      (continuous_circleMap 0 1)).intervalIntegrable _ _
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp ((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ)
  have h := L.circleAverage_comp_comm hi
  rw [avg_affine] at h
  simpa [L, Function.comp_def] using h
end ReciprocityTheory.AnForm.A.PshInh

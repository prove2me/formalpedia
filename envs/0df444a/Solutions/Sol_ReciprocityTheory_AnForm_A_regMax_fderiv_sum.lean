-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.regMax_fderiv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:51:17.713302+00:00
-- url     : https://prove2.me/submissions/d7032521-1d3b-4c80-be67-6d14286e6897

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution [DecidableEq ι] {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    ∑ j, fderiv ℝ (regMax (ι := ι) η) t (Pi.single j 1) = 1 := by
  have hd : DifferentiableAt ℝ (regMax (ι := ι) η) t :=
    (regMax_contDiff hη).differentiable (by simp) t
  rw [← map_sum, Finset.univ_sum_single (fun _ : ι => (1 : ℝ))]
  have hl : HasDerivAt (fun c : ℝ => t + c • (fun _ : ι => (1 : ℝ))) (fun _ => 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (fun _ : ι => (1 : ℝ))).const_add t
  have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun c : ℝ => regMax η (t + c • (fun _ : ι => (1 : ℝ)))) 1 0 := by
    have e : (fun c : ℝ => regMax η (t + c • (fun _ : ι => (1 : ℝ)))) = fun c => regMax η t + c := by
      funext c; rw [← regMax_add_const]; congr 1; funext j; simp
    rw [e]; exact (hasDerivAt_id (0 : ℝ)).const_add _
  exact h1.unique h2
end ReciprocityTheory.AnForm.A

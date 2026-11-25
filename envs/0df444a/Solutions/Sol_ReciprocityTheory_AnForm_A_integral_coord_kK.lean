-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_coord_kK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:30.995117+00:00
-- url     : https://prove2.me/submissions/dfc2d90a-7eab-47ad-92d8-f56fed1ad5bd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_neg

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
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (i : ι) : ∫ h, h i * kK h = 0 := by
  have e := integral_neg_eq_self (fun h : ι → ℝ => h i * kK h) volume
  simp only [Pi.neg_apply, kK_neg, neg_mul, integral_neg] at e
  linarith
end ReciprocityTheory.AnForm.A

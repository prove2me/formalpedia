-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.kK_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:57:55.870003+00:00
-- url     : https://prove2.me/submissions/ef3924ce-f10f-464e-9990-e3760eccfc62

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__neg_e5a33706ada1

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
theorem _root_.solution (h : ι → ℝ) : kK (-h) = kK h := by
  simp only [kK, Pi.neg_apply, kθ_neg]
end ReciprocityTheory.AnForm.A

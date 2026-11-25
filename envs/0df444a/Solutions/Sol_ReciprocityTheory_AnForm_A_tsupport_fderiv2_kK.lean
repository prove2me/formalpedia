-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tsupport_fderiv2_kK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:05.495006+00:00
-- url     : https://prove2.me/submissions/6ffefaac-be91-47a1-8ccb-13783889744f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_le_of_kK_ne


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
theorem _root_.solution :
    tsupport (fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ))) ⊆ closedBall 0 (1 / 2) :=
  (tsupport_fderiv_subset ℝ).trans ((tsupport_fderiv_subset ℝ).trans
    (closure_minimal (fun h hh => mem_closedBall_zero_iff.2 (norm_le_of_kK_ne hh))
      isClosed_closedBall))
end ReciprocityTheory.AnForm.A

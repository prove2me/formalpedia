-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.tmax_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:03.356675+00:00
-- url     : https://prove2.me/submissions/fa39d61d-b7c7-4619-b41d-18a1430d4359

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_tmax


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
theorem _root_.solution : tmax (0 : ι → ℝ) = 0 := by
  obtain ⟨i, hi⟩ := exists_tmax (0 : ι → ℝ); simpa using hi
end ReciprocityTheory.AnForm.A

-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.kK_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:54:41.412447+00:00
-- url     : https://prove2.me/submissions/84b7357f-981a-4a5a-bcda-b6104ac42cdc

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
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
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : HasCompactSupport (kK : (ι → ℝ) → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) (1 / 2)) fun h hh => ?_
  by_contra hne
  exact hh (mem_closedBall_zero_iff.2 (norm_le_of_kK_ne hne))
end ReciprocityTheory.AnForm.A

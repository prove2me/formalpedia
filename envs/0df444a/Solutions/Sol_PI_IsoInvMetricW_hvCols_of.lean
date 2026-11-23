-- Prove2me | solution 1 for PI.IsoInvMetricW.hvCols_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:15.562047+00:00
-- url     : https://prove2.me/submissions/884140c9-0c43-4dee-ba23-66d64633e4c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
namespace PI.IsoInvMetricW
theorem _root_.solution (hM : HvMap) : HvCols := by
  intro Lt _ _ N nu k
  unfold u0
  rw [hM]
  congr 1
  funext s a j
  unfold fr colsOf
  by_cases hj : j < N
  · simp [hj, Matrix.one_apply]
  · simp [hj]
end PI.IsoInvMetricW

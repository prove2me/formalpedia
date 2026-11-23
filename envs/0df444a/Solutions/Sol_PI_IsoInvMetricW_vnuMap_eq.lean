-- Prove2me | solution 1 for PI.IsoInvMetricW.vnuMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:19.322921+00:00
-- url     : https://prove2.me/submissions/2220315e-de53-4075-8664-ebeb35019567

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
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoInvMetricW
theorem _root_.solution (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ : LaC N nu) (I : ColChoice N nu) :
    VnuMap nu f φ I = ∑ J, E nu f I J * φ J := by
  unfold VnuMap
  rw [finsum_eq_sum_of_fintype]
  rfl
end PI.IsoInvMetricW

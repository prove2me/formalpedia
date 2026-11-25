-- Prove2me | solution 1 for PI.IsoInvMetricW.eStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:18.088172+00:00
-- url     : https://prove2.me/submissions/b54560d8-5571-422a-8b0d-30f3229ce0d1

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
theorem _root_.solution (k : Lt → Matrix (Fin N) (Fin N) ℂ) (I J : ColChoice N nu) :
    starRingEnd ℂ (E nu k I J) = E nu (fun s => star (k s)) J I := by
  unfold E
  simp only [map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [starRingEnd_apply, ← Matrix.det_conjTranspose]
  congr 1
end PI.IsoInvMetricW

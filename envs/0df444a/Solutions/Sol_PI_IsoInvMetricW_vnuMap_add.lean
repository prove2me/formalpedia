-- Prove2me | solution 1 for PI.IsoInvMetricW.vnuMap_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:50:03.593708+00:00
-- url     : https://prove2.me/submissions/735cc7a6-943e-4d94-b10f-a6af79592178

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_eq

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
theorem _root_.solution (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ ψ : LaC N nu) :
    VnuMap nu f (φ + ψ) = VnuMap nu f φ + VnuMap nu f ψ := by
  funext I
  simp only [vnuMap_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]
end PI.IsoInvMetricW

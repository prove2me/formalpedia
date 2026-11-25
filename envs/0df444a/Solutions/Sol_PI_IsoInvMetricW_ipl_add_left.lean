-- Prove2me | solution 1 for PI.IsoInvMetricW.ipl_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:44:53.201014+00:00
-- url     : https://prove2.me/submissions/66848d5c-23be-486a-aa93-d8856bcad6a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_SymmetricMeasureL2NormEqResolutionL2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoInvMetricW
theorem _root_.solution (φ φ' ψ : LaC N nu) : ipl (φ + φ') ψ = ipl φ ψ + ipl φ' ψ := by
  simp [ipl, add_mul, Finset.sum_add_distrib]
end PI.IsoInvMetricW

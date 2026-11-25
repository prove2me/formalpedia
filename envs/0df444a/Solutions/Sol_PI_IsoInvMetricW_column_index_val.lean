-- Prove2me | solution 1 for PI.IsoInvMetricW.column_index_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:59:04.823461+00:00
-- url     : https://prove2.me/submissions/209c9432-c8b7-4338-967e-a8dde88f900d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical Finset PI.IsoInvMetric Polynomial
open PI PI.IsoInvMetricW
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoInvMetricW
theorem _root_.solution (hle : ∀ z, (nu z).colLen 0 ≤ N) (s : Lt) (c : Fin ((nu s).rowLen 0))
    (i : Fin ((nu s).colLen c)) : ((J0 nu hle s c i : Fin N) : ℕ) = i := by
  simp [J0]
end PI.IsoInvMetricW

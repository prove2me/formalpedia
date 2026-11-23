-- Prove2me | solution 1 for PI.IsoInvMetricW.star_mul_self_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:31.328043+00:00
-- url     : https://prove2.me/submissions/2e077112-5d1c-4ebb-86a7-390e2fcc986a

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
namespace PI.IsoInvMetricW
theorem _root_.solution {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  have h := Complex.conj_mul' z
  rw [hz] at h
  simpa using h
end PI.IsoInvMetricW

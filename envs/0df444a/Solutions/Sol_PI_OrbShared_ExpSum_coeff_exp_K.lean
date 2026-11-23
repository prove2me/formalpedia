-- Prove2me | solution 1 for PI.OrbShared.ExpSum.coeff_exp_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:27.464104+00:00
-- url     : https://prove2.me/submissions/10997829-991a-4fac-8a9f-8bba0fe5d8ea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.OrbShared PI.OrbShared.ExpSum
open MvPowerSeries
variable {K : Type*} [Field K] [CharZero K]
namespace PI.OrbShared.ExpSum
theorem _root_.solution (n : ℕ) : PowerSeries.coeff n (PowerSeries.exp K) = ((n.factorial : K))⁻¹ := by
  simp [PowerSeries.coeff_exp]
end PI.OrbShared.ExpSum

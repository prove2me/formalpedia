-- Prove2me | solution 1 for PI.OrbShared.ExpSum.subst_eS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:27.651937+00:00
-- url     : https://prove2.me/submissions/33131c47-6cda-459a-a1d3-79ecb994d186

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
import Theorems.Thm_PI_OrbShared_ExpSum_subst_psubst

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
variable {τ υ : Type*}
namespace PI.OrbShared.ExpSum
theorem _root_.solution {b : τ → MvPowerSeries υ K} (hb : HasSubst b) (f : MvPowerSeries τ K)
    (hf : constantCoeff f = 0) : subst b (eS f) = eS (subst b f) := by
  exact subst_psubst hb (PowerSeries.HasSubst.of_constantCoeff_zero hf) _
end PI.OrbShared.ExpSum

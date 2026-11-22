-- Prove2me | solution 1 for PI.OrbShared.ExpSum.subst_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:10.097802+00:00
-- url     : https://prove2.me/submissions/b1746a3f-8a9b-43f7-ae13-d2890e494c60

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
variable {τ υ : Type*}
namespace PI.OrbShared.ExpSum
theorem _root_.solution {b : τ → MvPowerSeries υ K} (hb : HasSubst b) {a : MvPowerSeries τ K}
    (ha : PowerSeries.HasSubst a) (φ : PowerSeries K) :
    subst b (PowerSeries.subst a φ) = PowerSeries.subst (subst b a) φ := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb]
end PI.OrbShared.ExpSum

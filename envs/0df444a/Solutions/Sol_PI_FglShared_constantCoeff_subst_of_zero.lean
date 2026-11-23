-- Prove2me | solution 1 for PI.FglShared.constantCoeff_subst_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:07.889603+00:00
-- url     : https://prove2.me/submissions/5d597ab6-4477-4a6b-8ce8-9997cc3b3633

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglShared
open MvPowerSeries
variable {K : Type} [Field K] [CharZero K]
namespace PI.FglShared
theorem _root_.solution {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (f : PowerSeries K) : constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [ha, hd]
end PI.FglShared

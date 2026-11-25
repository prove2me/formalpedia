-- Prove2me | solution 1 for PI.FglShared.derivative_log_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:54.314705+00:00
-- url     : https://prove2.me/submissions/5fc2c647-1de7-4479-a71d-9a810a78fbdc

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
theorem _root_.solution : PowerSeries.derivative K (PowerSeries.log K) = (1 + PowerSeries.X)⁻¹ := by
  rw [PowerSeries.deriv_log, PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  ext n
  rcases n with _ | n
  · rw [mul_add, mul_one, map_add, PowerSeries.coeff_zero_mul_X, add_zero, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, if_pos rfl]
    simp
  · rw [mul_add, mul_one, map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), ← map_add]
    simp [pow_succ]
end PI.FglShared

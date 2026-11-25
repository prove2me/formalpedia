-- Prove2me | solution 1 for PI.FglShared.exp_subst_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:53:35.571312+00:00
-- url     : https://prove2.me/submissions/5738c12c-8128-42c3-a7c1-213fb4158fac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Theorems.Thm_PI_FglShared_constantCoeff_subst_of_zero
import Theorems.Thm_PI_FglShared_eq_one_add_X_of_deriv
import Theorems.Thm_PI_FglShared_derivative_log_eq

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
theorem _root_.solution :
    PowerSeries.subst (PowerSeries.log K) (PowerSeries.exp K) = (1 + PowerSeries.X : PowerSeries K) := by
  apply eq_one_add_X_of_deriv
  · rw [PowerSeries.derivative_subst PowerSeries.HasSubst.log, PowerSeries.derivative_exp,
      derivative_log_eq]
  · have h := constantCoeff_subst_of_zero (τ := Unit) (a := PowerSeries.log K)
      PowerSeries.constantCoeff_log (PowerSeries.exp K)
    rw [PowerSeries.constantCoeff_exp] at h
    exact h
end PI.FglShared

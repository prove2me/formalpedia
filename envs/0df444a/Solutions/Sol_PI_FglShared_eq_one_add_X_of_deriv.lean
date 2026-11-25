-- Prove2me | solution 1 for PI.FglShared.eq_one_add_X_of_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:57.080078+00:00
-- url     : https://prove2.me/submissions/680cfaa4-26e1-4178-ac60-d293c52aa06c

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
theorem _root_.solution {g : PowerSeries K}
    (hd : PowerSeries.derivative K g = g * (1 + PowerSeries.X)⁻¹)
    (h0 : PowerSeries.constantCoeff g = 1) : g = 1 + PowerSeries.X := by
  have hu : PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries K) ≠ 0 := by simp
  have hinv := PowerSeries.inv_mul_cancel _ hu
  have hD : PowerSeries.derivative K (g * (1 + PowerSeries.X)⁻¹) = PowerSeries.derivative K 1 := by
    simp only [Derivation.leibniz, PowerSeries.derivative_inv', hd, map_add,
      Derivation.map_one_eq_zero, PowerSeries.derivative_X, smul_eq_mul, zero_add]
    ring
  have hc : PowerSeries.constantCoeff (g * (1 + PowerSeries.X)⁻¹) =
      PowerSeries.constantCoeff (1 : PowerSeries K) := by
    simp [PowerSeries.constantCoeff_inv, h0]
  have h1 := PowerSeries.derivative.ext hD hc
  calc g = g * ((1 + PowerSeries.X)⁻¹ * (1 + PowerSeries.X)) := by rw [hinv, mul_one]
    _ = (g * (1 + PowerSeries.X)⁻¹) * (1 + PowerSeries.X) := by ring
    _ = 1 + PowerSeries.X := by rw [h1, one_mul]
end PI.FglShared

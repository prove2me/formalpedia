-- Prove2me | solution 1 for PI.OrbShared.ExpSum.eS_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:22.659549+00:00
-- url     : https://prove2.me/submissions/ee2d7d28-8171-4d17-a54b-e904c3b261a6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_ExpSum
import Theorems.Thm_PI_OrbShared_ExpSum_coeff_exp_K

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
theorem _root_.solution : eS (0 : MvPowerSeries τ K) = 1 := by
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), finsum_eq_single _ 0]
  · simp [coeff_exp_K]
  · intro d hd
    simp [zero_pow hd]
end PI.OrbShared.ExpSum

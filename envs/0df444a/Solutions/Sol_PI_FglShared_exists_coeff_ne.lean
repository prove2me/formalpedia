-- Prove2me | solution 1 for PI.FglShared.exists_coeff_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:47.40282+00:00
-- url     : https://prove2.me/submissions/c59ad3db-e173-4610-b7f7-9c40d847b892

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Theorems.Thm_PI_FglShared_l_constantCoeff
import Theorems.Thm_PI_FglShared_l_ne_zero

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
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglShared
theorem _root_.solution {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : ∃ k, k ≠ 0 ∧ PowerSeries.coeff k l ≠ 0 := by
  have hl0 := l_constantCoeff hex0 hinv
  by_contra hc
  push Not at hc
  apply l_ne_zero hex0 hinv
  ext k
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using hl0
  · simpa using hc k hk
end PI.FglShared

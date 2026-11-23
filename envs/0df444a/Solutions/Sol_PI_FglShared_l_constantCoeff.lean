-- Prove2me | solution 1 for PI.FglShared.l_constantCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:52.344282+00:00
-- url     : https://prove2.me/submissions/02506cbf-912f-4466-a26f-46e3ee1bd247

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Theorems.Thm_PI_FglShared_constantCoeff_subst_of_zero


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
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h := constantCoeff_subst_of_zero (a := ex) hex0 l
  rw [hinv] at h
  rw [← h]
  exact PowerSeries.constantCoeff_X
end PI.FglShared

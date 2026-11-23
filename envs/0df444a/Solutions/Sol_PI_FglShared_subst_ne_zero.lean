-- Prove2me | solution 1 for PI.FglShared.subst_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:40.304909+00:00
-- url     : https://prove2.me/submissions/3534ba91-2af0-43ab-9396-650e8fe94494

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Theorems.Thm_PI_FglShared_l_constantCoeff
import Theorems.Thm_PI_FglShared_subst_subst_eq

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
theorem _root_.solution {σ : Type} {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) {y : MvPowerSeries σ ℂ_[p]}
    (hy : constantCoeff y = 0) (hne : y ≠ 0) : PowerSeries.subst y ex ≠ 0 := by
  intro h0
  have h := subst_subst_eq hex0 hinv hy
  rw [h0, PowerSeries.subst_zero_of_constantCoeff_zero (l_constantCoeff hex0 hinv)] at h
  exact hne h.symm
end PI.FglShared

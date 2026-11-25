-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.TayInvPow.F_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:43:22.323724+00:00
-- url     : https://prove2.me/submissions/610d9b96-88bd-4fc2-9ca6-b7fa75772516

import Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TaylorInversePower_SumMultinomialSub
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_deg_eq_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_TayInvPow_coeff_F

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TayInvPow
open MvPowerSeries
variable {σ : Type*} {A : Type*} [CommRing A]
namespace PI.UnitaryGroupMassFormula.TayInvPow
theorem _root_.solution (c : σ →₀ A) (t : A) : F c t 0 = 1 := by
  classical
  ext β
  rw [coeff_F, coeff_one]
  split_ifs with h
  · subst h
    simp [cf, deg, cprod]
  · obtain ⟨m, hm⟩ : ∃ m, deg β = m + 1 := ⟨deg β - 1, by have := mt deg_eq_zero.1 h; omega⟩
    simp [cf, hm]
end PI.UnitaryGroupMassFormula.TayInvPow

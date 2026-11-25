-- Prove2me | solution 1 for PI.FglShared.coeff_single_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:50.999791+00:00
-- url     : https://prove2.me/submissions/307f4755-b40d-4870-8c23-a62896cfce1a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg

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
theorem _root_.solution {σ : Type} [DecidableEq σ] (l : PowerSeries ℂ_[p]) (i j : σ) {k : ℕ}
    (hk : k ≠ 0) : coeff (Finsupp.single i k) (PowerSeries.subst (X j : MvPowerSeries σ ℂ_[p]) l) =
      if j = i then PowerSeries.coeff k l else 0 := by
  rw [PowerSeries.coeff_subst_single]
  by_cases hji : j = i
  · subst hji
    simp
  · have hne : Finsupp.single i k ≠ Finsupp.single j ((Finsupp.single i k) j) := by
      rw [Finsupp.single_apply, if_neg (Ne.symm hji), Finsupp.single_zero]
      exact Finsupp.single_ne_zero.mpr hk
    rw [if_neg hne, if_neg hji]
end PI.FglShared

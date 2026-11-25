-- Prove2me | solution 1 for PI.FglShared.expMv_logS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:01:29.964958+00:00
-- url     : https://prove2.me/submissions/e18444d0-4ce9-4437-9139-1b8e8411dfc0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog
import Theorems.Thm_PI_FglShared_exp_subst_log
import Theorems.Thm_PI_FglShared_constantCoeff_logS
import Theorems.Thm_PI_FglShared_logS_eq_subst
import Theorems.Thm_PI_FglPhSplit_Wk_expMv_eq_subst


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
theorem _root_.solution {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : constantCoeff F = 1) :
    PI.FglPhSplit.expMv (logS F) = F := by
  have hF' : constantCoeff (F - 1) = 0 := by simp [hF]
  have ha : PowerSeries.HasSubst (F - 1) := PowerSeries.HasSubst.of_constantCoeff_zero hF'
  have h1 : PowerSeries.subst (F - 1) (1 : PowerSeries ℂ_[p]) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  rw [PI.FglPhSplit.Wk.expMv_eq_subst (constantCoeff_logS F), logS_eq_subst hF,
    ← PowerSeries.subst_comp_subst_apply PowerSeries.HasSubst.log ha, exp_subst_log,
    PowerSeries.subst_add ha, PowerSeries.subst_X ha, h1]
  ring
end PI.FglShared

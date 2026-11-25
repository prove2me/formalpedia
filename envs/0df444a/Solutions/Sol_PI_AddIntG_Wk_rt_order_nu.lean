-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_order_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:50.68125+00:00
-- url     : https://prove2.me/submissions/bc4e0581-b2f4-4ac0-8658-5a6c302327f6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_two_le_mul_right
import Theorems.Thm_PI_AddIntG_Wk_rt_two_le_sub
import Theorems.Thm_PI_AddIntG_Wk_rt_one_le_X
import Theorems.Thm_PI_AddIntG_Wk_rt_two_le_mul_X
import Theorems.Thm_PI_AddIntG_Wk_rt_order_lam
import Theorems.Thm_PI_AddIntG_Wk_rt_wv

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
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution (wq : PowerSeries ℂ_[p]) : 2 ≤ (nu wq).order := by
  have h3 : 2 ≤ ((Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 3).order := by
    rw [pow_succ]
    exact rt_two_le_mul_right _ _ (by rw [pow_two]; exact rt_two_le_mul_X (rt_one_le_X 0) 0)
  unfold nu
  rw [rt_wv]
  exact rt_two_le_sub (rt_two_le_mul_right _ _ h3) (rt_two_le_mul_right _ _ (rt_order_lam wq))
end PI.AddIntG.Wk

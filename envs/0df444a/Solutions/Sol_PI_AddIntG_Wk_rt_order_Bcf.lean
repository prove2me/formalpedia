-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_order_Bcf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:31.879385+00:00
-- url     : https://prove2.me/submissions/d0dd0a7b-08a1-4f08-af8b-e49bee602e72

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_two_le_mul_left
import Theorems.Thm_PI_AddIntG_Wk_rt_two_le_add
import Theorems.Thm_PI_AddIntG_Wk_rt_order_lam
import Theorems.Thm_PI_AddIntG_Wk_rt_order_nu

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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : 2 ≤ (Bcf W wq).order := by
  unfold Bcf
  have hl := rt_order_lam wq
  have hn := rt_order_nu wq
  have hl2 : 2 ≤ (lam wq ^ 2).order := by rw [pow_two]; exact rt_two_le_mul_left _ _ hl
  refine rt_two_le_add (rt_two_le_add (rt_two_le_add (rt_two_le_add ?_ ?_) ?_) ?_) ?_
  · exact rt_two_le_mul_left _ _ hl
  · exact rt_two_le_mul_left _ _ hn
  · exact rt_two_le_mul_left _ _ hl2
  · exact rt_two_le_mul_left _ _ hn
  · exact rt_two_le_mul_left _ _ hn
end PI.AddIntG.Wk

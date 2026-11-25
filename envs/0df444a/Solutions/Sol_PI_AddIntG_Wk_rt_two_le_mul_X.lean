-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_two_le_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:44.651625+00:00
-- url     : https://prove2.me/submissions/54a3df1b-fb4f-424a-842e-87d0c6f32b8f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_one_le_X

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
variable {σ : Type*}
namespace PI.AddIntG.Wk
theorem _root_.solution {f : MvPowerSeries σ ℂ_[p]} (hf : 1 ≤ f.order) (i : σ) :
    2 ≤ (f * Xv i).order := by
  have h2 : (2 : ℕ∞) ≤ f.order + (Xv i : MvPowerSeries σ ℂ_[p]).order :=
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ _ := add_le_add hf (rt_one_le_X i)
  first
    | exact h2.trans (MvPowerSeries.le_order_mul ..)
    | exact h2.trans (MvPowerSeries.order_mul_ge ..)
    | exact h2.trans (MvPowerSeries.add_order_le_order_mul ..)
end PI.AddIntG.Wk

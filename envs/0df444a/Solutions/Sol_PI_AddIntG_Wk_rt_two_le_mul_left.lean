-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_two_le_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:47.165396+00:00
-- url     : https://prove2.me/submissions/56daab7b-72fd-4813-b006-ea4bdeeae4f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero

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
theorem _root_.solution (f g : MvPowerSeries σ ℂ_[p]) (hg : 2 ≤ g.order) : 2 ≤ (f * g).order := by
  first
    | exact (hg.trans le_add_self).trans (MvPowerSeries.le_order_mul ..)
    | exact (hg.trans le_add_self).trans (MvPowerSeries.order_mul_ge ..)
    | exact (hg.trans le_add_self).trans (MvPowerSeries.add_order_le_order_mul ..)
end PI.AddIntG.Wk

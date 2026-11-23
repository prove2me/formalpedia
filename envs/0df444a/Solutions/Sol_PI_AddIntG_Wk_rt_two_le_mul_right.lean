-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_two_le_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:46.471331+00:00
-- url     : https://prove2.me/submissions/5e939971-8f70-40e1-ac36-58cc15a90851

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
theorem _root_.solution (f g : MvPowerSeries σ ℂ_[p]) (hf : 2 ≤ f.order) : 2 ≤ (f * g).order := by
  first
    | exact (hf.trans le_self_add).trans (MvPowerSeries.le_order_mul ..)
    | exact (hf.trans le_self_add).trans (MvPowerSeries.order_mul_ge ..)
    | exact (hf.trans le_self_add).trans (MvPowerSeries.add_order_le_order_mul ..)
end PI.AddIntG.Wk

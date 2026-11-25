-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_two_le_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:01:50.831074+00:00
-- url     : https://prove2.me/submissions/ac8d3650-5617-4995-a34d-21f2158d6968

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
theorem _root_.solution {f : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) : 2 ≤ (-f).order := by
  rw [MvPowerSeries.order_neg]
  exact hf
end PI.AddIntG.Wk

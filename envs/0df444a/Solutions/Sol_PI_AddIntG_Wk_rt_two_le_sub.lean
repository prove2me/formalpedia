-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_two_le_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:18.580627+00:00
-- url     : https://prove2.me/submissions/475d596c-c1e7-4f27-96a1-10bc63e147aa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_two_le_add
import Theorems.Thm_PI_AddIntG_Wk_rt_two_le_neg

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
theorem _root_.solution {f g : MvPowerSeries σ ℂ_[p]} (hf : 2 ≤ f.order) (hg : 2 ≤ g.order) :
    2 ≤ (f - g).order := by
  rw [sub_eq_add_neg]
  exact rt_two_le_add hf (rt_two_le_neg hg)
end PI.AddIntG.Wk

-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_one_le_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.884799+00:00
-- url     : https://prove2.me/submissions/8e407921-56be-4992-994a-1a482fe083a9

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
theorem _root_.solution (i : σ) : 1 ≤ (Xv i : MvPowerSeries σ ℂ_[p]).order := by
  refine MvPowerSeries.le_order fun d hd => ?_
  rw [MvPowerSeries.coeff_X, if_neg]
  rintro rfl
  simp at hd
end PI.AddIntG.Wk

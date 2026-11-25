-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_Acf_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:33.845536+00:00
-- url     : https://prove2.me/submissions/d6eaa821-e9ed-4324-bb70-a675a7db4178

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_Acf

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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.constantCoeff (Acf W wq) ≠ 0 := by
  rw [constantCoeff_Acf]
  exact one_ne_zero
end PI.AddIntG.Wk

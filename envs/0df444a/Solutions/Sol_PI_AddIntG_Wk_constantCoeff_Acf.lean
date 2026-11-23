-- Prove2me | solution 1 for PI.AddIntG.Wk.constantCoeff_Acf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:06.534923+00:00
-- url     : https://prove2.me/submissions/564ad8ea-9252-47b3-9500-ebc24887b39c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_constantCoeff_lam

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
    MvPowerSeries.constantCoeff (Acf W wq) = 1 := by
  simp [Acf, rt_constantCoeff_lam]
end PI.AddIntG.Wk

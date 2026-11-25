-- Prove2me | solution 1 for PI.AddIntG.Wk.vieta1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:20:12.420209+00:00
-- url     : https://prove2.me/submissions/a7098949-739c-4520-97b9-b1fdff693946

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_Acf_ne

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
    Acf W wq * (Xv 0 + Xv 1 + Z3 W wq) = -Bcf W wq := by
  have hA : Acf W wq * (Acf W wq)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (rt_Acf_ne W wq)
  unfold Z3
  linear_combination (-(Bcf W wq)) * hA
end PI.AddIntG.Wk

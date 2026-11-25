-- Prove2me | solution 1 for PI.AddIntG.Wk.thirdRoot_sub_var_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:08:05.632613+00:00
-- url     : https://prove2.me/submissions/6c6ccb6f-e95d-474b-8eb4-a27258be219b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_rt_coeff_BA

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
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Z3 W wq - Xv 1 ≠ 0 := by
  have hs : Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single 1 1 := by
    rw [Ne, Finsupp.single_left_inj one_ne_zero]
    decide
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h0
  simp [Z3, rt_coeff_BA, MvPowerSeries.coeff_X, hs, hs.symm] at h1
end PI.AddIntG.Wk

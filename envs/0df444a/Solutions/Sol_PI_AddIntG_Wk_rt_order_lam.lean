-- Prove2me | solution 1 for PI.AddIntG.Wk.rt_order_lam
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:51.199124+00:00
-- url     : https://prove2.me/submissions/24e52d7e-1dc2-4c24-a597-c941aa4426fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_lam
import Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_wser


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
theorem _root_.solution (wq : PowerSeries ℂ_[p]) : 2 ≤ (lam wq).order := by
  refine MvPowerSeries.le_order fun e he => ?_
  have hd : e 0 + e 1 < 2 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at he
    exact_mod_cast he
  rw [lamA_coeff_lam, lamA_coeff_wser, if_neg (by omega)]
end PI.AddIntG.Wk

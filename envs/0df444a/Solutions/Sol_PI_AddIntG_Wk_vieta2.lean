-- Prove2me | solution 1 for PI.AddIntG.Wk.vieta2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:22.39702+00:00
-- url     : https://prove2.me/submissions/3b0340cb-4dfc-4fad-a270-447b9448fbe4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_vieta1
import Theorems.Thm_PI_AddIntG_Wk_var_zero_sub_var_one_ne_zero
import Theorems.Thm_PI_AddIntG_Wk_chordCubic_var_zero
import Theorems.Thm_PI_AddIntG_Wk_chordCubic_var_one

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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    Ccf W wq = Acf W wq * (Xv 0 * Xv 1 + Xv 0 * Z3 W wq + Xv 1 * Z3 W wq) := by
  have hK : Acf W wq * (Xv 0 ^ 2 + Xv 0 * Xv 1 + Xv 1 ^ 2) + Bcf W wq * (Xv 0 + Xv 1) + Ccf W wq = 0 := by
    have hprod : (Xv 0 - Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) *
        (Acf W wq * (Xv 0 ^ 2 + Xv 0 * Xv 1 + Xv 1 ^ 2) + Bcf W wq * (Xv 0 + Xv 1) + Ccf W wq) = 0 := by
      linear_combination chordCubic_var_zero h - chordCubic_var_one h
    exact (mul_eq_zero.1 hprod).resolve_left var_zero_sub_var_one_ne_zero
  linear_combination hK - (Xv 0 + Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) * vieta1 W wq
end PI.AddIntG.Wk

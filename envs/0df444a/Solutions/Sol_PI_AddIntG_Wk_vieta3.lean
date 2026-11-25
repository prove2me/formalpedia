-- Prove2me | solution 1 for PI.AddIntG.Wk.vieta3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:06:10.675282+00:00
-- url     : https://prove2.me/submissions/82f86e5a-0839-42cc-8dcf-f04f8935c06d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Theorems.Thm_PI_AddIntG_Wk_vieta1
import Theorems.Thm_PI_AddIntG_Wk_chordCubic_var_zero
import Theorems.Thm_PI_AddIntG_Wk_vieta2

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
    Dcf W wq = -(Acf W wq * Xv 0 * Xv 1 * Z3 W wq) := by
  linear_combination chordCubic_var_zero h - (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * vieta1 W wq -
    (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * vieta2 h
end PI.AddIntG.Wk

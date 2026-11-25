-- Prove2me | solution 1 for PI.AddIntG.Wk.constantCoeff_Fch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:08:32.3198+00:00
-- url     : https://prove2.me/submissions/13577dfa-bc36-44a5-9582-6192221d5257

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Theorems.Thm_PI_AddIntG_Wk_bZ_const
import Theorems.Thm_PI_AddIntG_Wk_hasSubst_bZ
import Theorems.Thm_PI_AddIntG_Wk_Fch_eq
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_thirdRoot


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
    MvPowerSeries.constantCoeff (Fch W wq) = 0 := by
  rw [Fch_eq]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_bZ W wq) (bZ_const W wq) (constantCoeff_thirdRoot W wq)
end PI.AddIntG.Wk

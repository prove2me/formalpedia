-- Prove2me | solution 1 for PI.AddIntG.Wk.constantCoeff_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:29.635326+00:00
-- url     : https://prove2.me/submissions/6a396459-db5e-462a-a68a-866d098b59f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_wser
import Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_lam

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
theorem _root_.solution (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (lam wq) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lamA_coeff_lam, lamA_coeff_wser]
  simp
end PI.AddIntG.Wk

-- Prove2me | solution 1 for PI.AddIntG.Wk.bZ_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:13.478895+00:00
-- url     : https://prove2.me/submissions/73fe613c-4b2f-4b25-8c5a-7f9e603996ab

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
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
    ∀ i, MvPowerSeries.constantCoeff (bZ W wq i) = 0 := by
  intro i
  unfold bZ
  split_ifs
  · exact map_zero _
  · exact constantCoeff_thirdRoot W wq
end PI.AddIntG.Wk

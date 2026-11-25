-- Prove2me | solution 1 for PI.FglTriFactor.Wk.subst_lastVarSubst_liftedThirdRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:10.406657+00:00
-- url     : https://prove2.me/submissions/73e9d776-2e72-4269-bc2e-31a0530369d6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_h0X
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_zc
import Theorems.Thm_PI_FglTriFactor_Wk_pr_zero_zero
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_thirdRoot
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_FglTriFactor_Wk_pr_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglTriFactor.Wk
theorem _root_.solution (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst (zc (p := p)) (s3 W wq) = 0 := by
  rw [s3, pr_comp (hasSubst_zc (p := p)) (h0X 0) (h0X 1), MvPowerSeries.subst_X (hasSubst_zc (p := p)), MvPowerSeries.subst_X (hasSubst_zc (p := p))]
  exact pr_zero_zero _ (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq)
end PI.FglTriFactor.Wk

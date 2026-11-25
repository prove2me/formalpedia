-- Prove2me | solution 1 for PI.FglTriFactor.Wk.mu_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:26.595336+00:00
-- url     : https://prove2.me/submissions/8799d229-e88a-41ed-adce-fef8e0d0575c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_h0X
import Theorems.Thm_PI_FglTriFactor_Wk_lam_as
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_FglTriFactor_Wk_constantCoeff_liftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_upd
import Theorems.Thm_PI_FglTriFactor_Wk_liftedThirdRoot_sub_X_one_ne_zero
import Theorems.Thm_PI_FglTriFactor_Wk_pr_comp
import Theorems.Thm_PI_FglTriFactor_Wk_subst_sub
import Theorems.Thm_PI_FglTriFactor_Wk_upd_ne
import Theorems.Thm_PI_FglTriFactor_Wk_upd_self


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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {μ : MvPowerSeries (Fin 3) ℂ_[p]} (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    MvPowerSeries.subst (upd 2 (s3 W wq)) μ = 0 := by
  have Hφ := hasSubst_upd (2 : Fin 3) (constantCoeff_liftedThirdRoot W wq)
  have e := congrArg (MvPowerSeries.subst (upd 2 (s3 W wq))) hμ
  rw [MvPowerSeries.subst_sub Hφ, MvPowerSeries.subst_mul Hφ, MvPowerSeries.subst_sub Hφ, Lac, Lab,
    pr_comp Hφ (h0X 0) (h0X 2), pr_comp Hφ (h0X 0) (h0X 1), MvPowerSeries.subst_X Hφ, MvPowerSeries.subst_X Hφ,
    MvPowerSeries.subst_X Hφ, upd_ne _ (by decide : (0 : Fin 3) ≠ 2), upd_ne _ (by decide : (1 : Fin 3) ≠ 2),
    upd_self] at e
  rw [← Lab, lam_as h, sub_self] at e
  exact (mul_eq_zero.1 e.symm).resolve_left (liftedThirdRoot_sub_X_one_ne_zero W wq)
end PI.FglTriFactor.Wk

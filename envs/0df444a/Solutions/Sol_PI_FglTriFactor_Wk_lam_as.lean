-- Prove2me | solution 1 for PI.FglTriFactor.Wk.lam_as
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:35.999727+00:00
-- url     : https://prove2.me/submissions/6264ae1d-1e0c-4acd-a66a-28b37e0ad6f9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_h0X
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_thirdRoot
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_subst_thirdRoot_wSeries
import Theorems.Thm_PI_FglTriFactor_Wk_constantCoeff_liftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_pr
import Theorems.Thm_PI_FglTriFactor_Wk_lam_pr
import Theorems.Thm_PI_FglTriFactor_Wk_liftedThirdRoot_sub_X_zero_ne_zero
import Theorems.Thm_PI_FglTriFactor_Wk_psubst_comm
import Theorems.Thm_PI_FglTriFactor_Wk_subst_add
import Theorems.Thm_PI_FglTriFactor_Wk_subst_sub


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
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (s3 W wq) (lam wq) = Lab wq := by
  have H := hasSubst_pr (h0X (p := p) 0) (h0X 1)
  have hl := lam_pr wq (h0X (p := p) 0) (constantCoeff_liftedThirdRoot W wq)
  have hZ0 := PI.AddIntG.Wk.constantCoeff_thirdRoot W wq
  have ws : PowerSeries.subst (s3 W wq) (wser wq) = Lab wq * s3 W wq + pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) (nu wq) := by
    rw [s3, pr, ← psubst_comm hZ0 H, PI.AddIntG.Wk.subst_thirdRoot_wSeries h, MvPowerSeries.subst_add H, MvPowerSeries.subst_mul H]
    rfl
  have hnu : pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1) (nu wq) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (wser wq) - Lab wq * MvPowerSeries.X 0 := by
    simp only [nu, wv, PI.AddIntG.Xv]
    rw [pr, MvPowerSeries.subst_sub H, MvPowerSeries.subst_mul H, psubst_comm (by simp) H, MvPowerSeries.subst_X H]
    rfl
  rw [ws, hnu] at hl
  have key : (s3 W wq - MvPowerSeries.X 0) *
      (pr (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (s3 W wq) (lam wq) - Lab wq) = 0 := by
    linear_combination hl
  exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (liftedThirdRoot_sub_X_zero_ne_zero W wq))
end PI.FglTriFactor.Wk

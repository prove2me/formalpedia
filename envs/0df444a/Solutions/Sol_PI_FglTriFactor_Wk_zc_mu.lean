-- Prove2me | solution 1 for PI.FglTriFactor.Wk.zc_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:29.54054+00:00
-- url     : https://prove2.me/submissions/2cf38f76-a16f-456b-956d-e72785815e4b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_h0X
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_zc
import Theorems.Thm_PI_FglTriFactor_Wk_pr_zero_zero
import Theorems.Thm_PI_FglTriFactor_Wk_eq_of_X_two_mul_eq
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_lam
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_FglTriFactor_Wk_cc_wser
import Theorems.Thm_PI_FglTriFactor_Wk_lam_pr
import Theorems.Thm_PI_FglTriFactor_Wk_pr_comp
import Theorems.Thm_PI_FglTriFactor_Wk_subst_sub
import Theorems.Thm_PI_FglTriFactor_Wk_wser_X


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
theorem _root_.solution {wq : PowerSeries ℂ_[p]} {μ : MvPowerSeries (Fin 3) ℂ_[p]}
    (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    MvPowerSeries.subst (zc (p := p)) μ = MvPowerSeries.X 2 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq := by
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hμ
  rw [MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_mul Hz, MvPowerSeries.subst_sub Hz, Lac, Lab,
    pr_comp Hz (h0X 0) (h0X 2), pr_comp Hz (h0X 0) (h0X 1), MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz,
    MvPowerSeries.subst_X Hz] at e
  have e0 : zc (p := p) 0 = 0 := rfl
  have e1 : zc (p := p) 1 = 0 := rfl
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e0, e1, e2, pr_zero_zero _ (PI.AddIntG.Wk.constantCoeff_lam wq), sub_zero, sub_zero] at e
  have hl := lam_pr wq (x := (0 : MvPowerSeries (Fin 3) ℂ_[p])) (y := MvPowerSeries.X 2) (by simp) (by simp)
  rw [PowerSeries.subst_zero_of_constantCoeff_zero (cc_wser wq), wser_X, sub_zero, sub_zero, e] at hl
  apply eq_of_X_two_mul_eq
  apply eq_of_X_two_mul_eq
  linear_combination hl
end PI.FglTriFactor.Wk

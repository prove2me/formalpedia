-- Prove2me | solution 1 for PI.FglTriFactor.Wk.m_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:55.734177+00:00
-- url     : https://prove2.me/submissions/2b698412-1b4d-4b01-9c50-20b756a69a38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_h0X
import Theorems.Thm_PI_FglTriFactor_Wk_mu_vanish
import Theorems.Thm_PI_FglTriFactor_Wk_subst_updateVar_two_liftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_liftedThirdRoot_mem_coeffSubring
import Theorems.Thm_PI_FglTriFactor_Wk_zc_const
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_zc
import Theorems.Thm_PI_FglTriFactor_Wk_subst_lastVarSubst_liftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_eq_of_X_two_mul_eq
import Theorems.Thm_PI_FglTriFactor_Wk_zc_mu
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_wq_const
import Theorems.Thm_PI_FglTriFactor_Wk_cc_subst_eq
import Theorems.Thm_PI_FglTriFactor_Wk_constantCoeff_liftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_fact_div
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
theorem _root_.solution {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq)
    {μ : MvPowerSeries (Fin 3) ℂ_[p]} (hμS : μ ∈ SerS S (Fin 3))
    (hμ : Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ) :
    ∃ m ∈ SerS S (Fin 3), MvPowerSeries.constantCoeff m = 1 ∧ μ = (MvPowerSeries.X 2 - s3 W wq) * m := by
  obtain ⟨m, hmS, hm⟩ := fact_div (k := 2) (constantCoeff_liftedThirdRoot W wq) (liftedThirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h) (subst_updateVar_two_liftedThirdRoot W wq) hμS
    (mu_vanish h hμ)
  refine ⟨m, hmS, ?_, hm⟩
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hm
  rw [zc_mu hμ, MvPowerSeries.subst_mul Hz, MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_X Hz, subst_lastVarSubst_liftedThirdRoot,
    sub_zero] at e
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e2] at e
  have e' := eq_of_X_two_mul_eq e
  rw [← cc_subst_eq Hz (zc_const (p := p)) m, ← e', PowerSeries.subst_def,
    cc_subst_eq (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => h0X (p := p) 2)) (fun _ => h0X (p := p) 2)]
  exact PI.AddIntG.Wk.wq_const h
end PI.FglTriFactor.Wk

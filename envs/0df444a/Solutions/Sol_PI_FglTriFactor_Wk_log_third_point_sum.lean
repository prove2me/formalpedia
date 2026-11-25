-- Prove2me | solution 1 for PI.FglTriFactor.Wk.log_third_point_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:04.212124+00:00
-- url     : https://prove2.me/submissions/58047f43-8425-4746-993e-4f3044033e30

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LogThirdPointSum
import Theorems.Thm_P2M_PI_FglTriFactor_Wk_abel__b380fdd8500c
import Theorems.Thm_PI_FglTriFactor_Wk_cc_X
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_thirdRoot
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_pr
import Theorems.Thm_PI_FglTriFactor_Wk_subst_add
import Theorems.Thm_PI_FglTriFactor_Wk_subst_lg


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
theorem _root_.solution {τ : Type*} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq)
    {x y : MvPowerSeries τ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    lg (flog W wq) (pr x y (Z3 W wq)) = -lg (flog W wq) x - lg (flog W wq) y := by
  have H := hasSubst_pr hx hy
  have e := congrArg (MvPowerSeries.subst ![x, y]) (abel' h)
  rw [MvPowerSeries.subst_add H, MvPowerSeries.subst_add H, subst_lg H (cc_X 0), subst_lg H (cc_X 1),
    subst_lg H (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq), MvPowerSeries.subst_X H, MvPowerSeries.subst_X H] at e
  have hz : MvPowerSeries.subst ![x, y] (0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom H, map_zero]
  rw [hz] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
  rw [pr]
  linear_combination e
end PI.FglTriFactor.Wk

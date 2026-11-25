-- Prove2me | solution 1 for PI.FglTriFactor.Wk.sub_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:58:14.880465+00:00
-- url     : https://prove2.me/submissions/32d46394-5b06-4e8b-b2e4-ddab40e4df91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LogThirdPointSum
import Theorems.Thm_PI_FglTriFactor_Wk_cc_flog
import Theorems.Thm_P2M_PI_FglTriFactor_Wk_inv__680ad30da99a
import Theorems.Thm_PI_FglTriFactor_Wk_cc_X
import Theorems.Thm_PI_FglTriFactor_Wk_log_third_point_sum
import Theorems.Thm_P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
import Theorems.Thm_PI_AddIntG_Wk_constantCoeff_thirdRoot
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_thirdRoot_mem_coeffSubring
import Theorems.Thm_PI_FglTriFactor_Wk_add_pr
import Theorems.Thm_PI_FglTriFactor_Wk_cc_pr
import Theorems.Thm_PI_FglTriFactor_Wk_cc_subst_eq
import Theorems.Thm_PI_FglTriFactor_Wk_fact_div
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_upd
import Theorems.Thm_PI_FglTriFactor_Wk_lg_zero
import Theorems.Thm_PI_FglTriFactor_Wk_pr_mem
import Theorems.Thm_PI_FglTriFactor_Wk_pt_lg
import Theorems.Thm_PI_FglTriFactor_Wk_pt_zero
import Theorems.Thm_PI_FglTriFactor_Wk_subst_sub
import Theorems.Thm_PI_FglTriFactor_Wk_upd_const
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
theorem _root_.solution {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq ex : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq)
    (hex0 : PowerSeries.constantCoeff ex = 0) (hex : PowerSeries.subst ex (flog W wq) = PowerSeries.X)
    (hF : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2)) :
    ∃ u ∈ SerS S (Fin 2), MvPowerSeries.constantCoeff u = 1 ∧
      sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * u := by
  have hl0 := cc_flog W wq
  have h0 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := map_zero _
  set Zn := pr (0 : MvPowerSeries (Fin 2) ℂ_[p]) (MvPowerSeries.X 1) (Z3 W wq) with hZn
  have hZn0 : MvPowerSeries.constantCoeff Zn = 0 := cc_pr h0 (cc_X 1) (PI.AddIntG.Wk.constantCoeff_thirdRoot W wq)
  have hZnS : Zn ∈ SerS S (Fin 2) :=
    pr_mem h0 (cc_X 1) (zero_mem _) (X_mem_SerS' S 1) (PI.AddIntG.Wk.thirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h)
  have hlZn : lg (flog W wq) Zn = -lg (flog W wq) (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) := by
    rw [hZn, log_third_point_sum h h0 (cc_X 1), lg_zero hl0, neg_zero, zero_sub]
  have hsa : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) =
      add (flog W wq) ex (MvPowerSeries.X 0) Zn := by
    unfold sub add; rw [hlZn, sub_eq_add_neg]
  have hGS : sub (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) := by
    rw [hsa, add_pr hl0 (cc_X 0) hZn0]
    exact pr_mem (cc_X 0) hZn0 (X_mem_SerS' S 0) hZnS hF
  have HU := hasSubst_upd (0 : Fin 2) (cc_X (p := p) (1 : Fin 2))
  obtain ⟨u, huS, hu⟩ := fact_div (k := 0) (cc_X 1) (X_mem_SerS' S 1)
    (fun t ht => by rw [MvPowerSeries.subst_X (hasSubst_upd 0 ht), upd_ne _ (by decide)]) hGS (by
      rw [subst_sub hl0 HU (cc_X 0) (cc_X 1), MvPowerSeries.subst_X HU, MvPowerSeries.subst_X HU, upd_self,
        upd_ne _ (by decide : (1 : Fin 2) ≠ 0)]
      unfold sub; rw [sub_self, pt_zero hex0])
  refine ⟨u, huS, ?_, hu⟩
  have H1 := hasSubst_upd (1 : Fin 2) h0
  have e := congrArg (MvPowerSeries.subst (upd (1 : Fin 2) (0 : MvPowerSeries (Fin 2) ℂ_[p]))) hu
  rw [subst_sub hl0 H1 (cc_X 0) (cc_X 1), MvPowerSeries.subst_mul H1, MvPowerSeries.subst_sub H1,
    MvPowerSeries.subst_X H1, MvPowerSeries.subst_X H1, upd_self, upd_ne _ (by decide : (0 : Fin 2) ≠ 1),
    sub_zero] at e
  have e' : sub (flog W wq) ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) 0 = MvPowerSeries.X 0 := by
    unfold sub; rw [lg_zero hl0, sub_zero, pt_lg hl0 (inv' h hex0 hex) (cc_X 0)]
  rw [e'] at e
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ≠ 0 := by
    intro h'
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)) h'
    simp [MvPowerSeries.coeff_X] at this
  have e2 : MvPowerSeries.X 0 * (MvPowerSeries.subst (upd (1 : Fin 2) (0 : MvPowerSeries (Fin 2) ℂ_[p])) u - 1) = 0 := by
    linear_combination -e
  have e3 := sub_eq_zero.1 ((mul_eq_zero.1 e2).resolve_left hX0)
  rw [← cc_subst_eq H1 (upd_const h0) u, e3, map_one]
end PI.FglTriFactor.Wk

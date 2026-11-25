-- Prove2me | solution 1 for PI.FglTriFactor.Wk.add_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:56:48.628114+00:00
-- url     : https://prove2.me/submissions/935cdce0-66de-4df4-9fd0-67a52de4ea56

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LogThirdPointSum
import Theorems.Thm_PI_FglTriFactor_Wk_cc_flog
import Theorems.Thm_P2M_PI_FglTriFactor_Wk_inv__680ad30da99a
import Theorems.Thm_PI_FglTriFactor_Wk_cc_X
import Theorems.Thm_PI_FglTriFactor_Wk_log_third_point_sum
import Theorems.Thm_P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_FglTriFactor_Wk_add_pr
import Theorems.Thm_PI_FglTriFactor_Wk_cc_add
import Theorems.Thm_PI_FglTriFactor_Wk_cc_lg
import Theorems.Thm_PI_FglTriFactor_Wk_cc_subst_eq
import Theorems.Thm_PI_FglTriFactor_Wk_constantCoeff_liftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_eq_of_X_two_mul_eq
import Theorems.Thm_PI_FglTriFactor_Wk_fact_div
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_upd
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_zc
import Theorems.Thm_PI_FglTriFactor_Wk_lg_pt
import Theorems.Thm_PI_FglTriFactor_Wk_lg_zero
import Theorems.Thm_PI_FglTriFactor_Wk_liftedThirdRoot_mem_coeffSubring
import Theorems.Thm_PI_FglTriFactor_Wk_pr_mem
import Theorems.Thm_PI_FglTriFactor_Wk_pt_lg
import Theorems.Thm_PI_FglTriFactor_Wk_pt_zero
import Theorems.Thm_PI_FglTriFactor_Wk_subst_add
import Theorems.Thm_PI_FglTriFactor_Wk_subst_lastVarSubst_liftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_subst_sub
import Theorems.Thm_PI_FglTriFactor_Wk_subst_updateVar_two_liftedThirdRoot
import Theorems.Thm_PI_FglTriFactor_Wk_upd_ne
import Theorems.Thm_PI_FglTriFactor_Wk_upd_self
import Theorems.Thm_PI_FglTriFactor_Wk_zc_const


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
    ∃ u ∈ SerS S (Fin 3), MvPowerSeries.constantCoeff u = 1 ∧
      add (flog W wq) ex (add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) (MvPowerSeries.X 2) =
        (MvPowerSeries.X 2 - s3 W wq) * u := by
  have hl0 := cc_flog W wq
  set l := flog W wq with hl
  have hab0 : MvPowerSeries.constantCoeff
      (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1)) = 0 :=
    cc_add hl0 hex0 (cc_X 0) (cc_X 1)
  have hGS : add l ex (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1))
      (MvPowerSeries.X 2) ∈ SerS S (Fin 3) := by
    rw [add_pr hl0 hab0 (cc_X 2), add_pr hl0 (cc_X 0) (cc_X 1)]
    have hab0' := hab0
    rw [add_pr hl0 (cc_X 0) (cc_X 1)] at hab0'
    exact pr_mem hab0' (cc_X 2) (pr_mem (cc_X 0) (cc_X 1) (X_mem_SerS' S 0) (X_mem_SerS' S 1) hF)
      (X_mem_SerS' S 2) hF
  have hlab : lg l (add l ex (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 1)) =
      lg l (MvPowerSeries.X 0) + lg l (MvPowerSeries.X 1) := by
    unfold add
    exact lg_pt hex0 hex (by rw [map_add, cc_lg hl0 (cc_X 0), cc_lg hl0 (cc_X 1), add_zero])
  have HU := hasSubst_upd (2 : Fin 3) (constantCoeff_liftedThirdRoot W wq)
  obtain ⟨u, huS, hu⟩ := fact_div (k := 2) (constantCoeff_liftedThirdRoot W wq) (liftedThirdRoot_mem_coeffSubring h1 h2 h3 h4 h6 h) (subst_updateVar_two_liftedThirdRoot W wq) hGS (by
      rw [subst_add hl0 HU hab0 (cc_X 2), subst_add hl0 HU (cc_X 0) (cc_X 1), MvPowerSeries.subst_X HU,
        MvPowerSeries.subst_X HU, MvPowerSeries.subst_X HU, upd_self, upd_ne _ (by decide : (0 : Fin 3) ≠ 2),
        upd_ne _ (by decide : (1 : Fin 3) ≠ 2)]
      have hZ := log_third_point_sum h (cc_X (p := p) (0 : Fin 3)) (cc_X 1)
      rw [← hl] at hZ
      change pt ex (lg l (add l ex (MvPowerSeries.X 0) (MvPowerSeries.X 1)) + lg l (s3 W wq)) = 0
      rw [hlab, s3, hZ]
      rw [show lg l (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) + lg l (MvPowerSeries.X 1) +
          (-lg l (MvPowerSeries.X 0) - lg l (MvPowerSeries.X 1)) = 0 by ring, pt_zero hex0])
  refine ⟨u, huS, ?_, hu⟩
  have Hz := hasSubst_zc (p := p)
  have e := congrArg (MvPowerSeries.subst (zc (p := p))) hu
  rw [subst_add hl0 Hz hab0 (cc_X 2), subst_add hl0 Hz (cc_X 0) (cc_X 1), MvPowerSeries.subst_mul Hz,
    MvPowerSeries.subst_sub Hz, MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz, MvPowerSeries.subst_X Hz,
    subst_lastVarSubst_liftedThirdRoot, sub_zero] at e
  have e0 : zc (p := p) 0 = 0 := rfl
  have e1 : zc (p := p) 1 = 0 := rfl
  have e2 : zc (p := p) 2 = MvPowerSeries.X 2 := rfl
  rw [e0, e1, e2] at e
  have e00 : add l ex (0 : MvPowerSeries (Fin 3) ℂ_[p]) 0 = 0 := by
    unfold add; rw [lg_zero hl0, add_zero, pt_zero hex0]
  have ec : add l ex (0 : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X 2) = MvPowerSeries.X 2 := by
    unfold add; rw [lg_zero hl0, zero_add, pt_lg hl0 (inv' h hex0 hex) (cc_X 2)]
  rw [e00, ec] at e
  have e' := eq_of_X_two_mul_eq (f := MvPowerSeries.subst (zc (p := p)) u) (g := 1) (by rw [mul_one]; exact e.symm)
  rw [← cc_subst_eq Hz (zc_const (p := p)) u, e', map_one]
end PI.FglTriFactor.Wk

-- Prove2me | solution 1 for PI.FglTriFactor.Wk.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:26.401745+00:00
-- url     : https://prove2.me/submissions/87de0061-8662-40de-8b74-4ec1d8beffea

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LogThirdPointSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_CcPrEq
import Theorems.Thm_PI_FglTriFactor_Wk_cc_pr_eq
import Theorems.Thm_P2M_PI_FglTriFactor_Wk_X_mem_SerS__cfa52566366e
import Theorems.Thm_PI_AddIntG_Wk_exists_intS
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_wq_mem
import Theorems.Thm_PI_FglTriFactor_Wk_T_eq
import Theorems.Thm_PI_FglTriFactor_Wk_add_factor
import Theorems.Thm_PI_FglTriFactor_Wk_cc_flog
import Theorems.Thm_PI_FglTriFactor_Wk_h0X
import Theorems.Thm_PI_FglTriFactor_Wk_hasSubst_pr
import Theorems.Thm_PI_FglTriFactor_Wk_m_exists
import Theorems.Thm_PI_FglTriFactor_Wk_mu_exists
import Theorems.Thm_PI_FglTriFactor_Wk_pr_mem
import Theorems.Thm_PI_FglTriFactor_Wk_sub_factor
import Theorems.Thm_PI_FglTriFactor_Wk_sub_pr
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
theorem _root_.solution : Lemma := by
  intro p _ W wq ex h1 h2 h3 h4 h6 _ hW hex0 hex hadd
  obtain ⟨S, hS⟩ := PI.AddIntG.Wk.exists_intS p
  have hS1 : W.a₁ ∈ S := (hS _).2 h1
  have hS2 : W.a₂ ∈ S := (hS _).2 h2
  have hS3 : W.a₃ ∈ S := (hS _).2 h3
  have hS4 : W.a₄ ∈ S := (hS _).2 h4
  have hS6 : W.a₆ ∈ S := (hS _).2 h6
  have hint : ∀ {σ : Type} (F : MvPowerSeries σ ℂ_[p]), IntegralMv F ↔ F ∈ SerS S σ := fun F => by
    rw [mem_SerS]
    exact forall_congr' fun e => (hS _).symm
  have hF : add (flog W wq) ex (MvPowerSeries.X 0) (MvPowerSeries.X 1) ∈ SerS S (Fin 2) := (hint _).1 hadd
  have hwq := PI.AddIntG.Wk.wq_mem hS1 hS2 hS3 hS4 hS6 hW
  obtain ⟨μ, hμS, hμ⟩ := mu_exists hwq
  obtain ⟨m, hmS, hm1, hmμ⟩ := m_exists hS1 hS2 hS3 hS4 hS6 hW hμS hμ
  obtain ⟨u1, hu1S, hu11, hu1⟩ := add_factor hS1 hS2 hS3 hS4 hS6 hW hex0 hex hF
  obtain ⟨u, huS, hu0, hu⟩ := sub_factor hS1 hS2 hS3 hS4 hS6 hW hex0 hex hF
  have hl0 := cc_flog W wq
  have hsub : ∀ i j : Fin 3, sub (flog W wq) ex (MvPowerSeries.X i) (MvPowerSeries.X j) =
      (MvPowerSeries.X i - MvPowerSeries.X j) * pr (MvPowerSeries.X i) (MvPowerSeries.X j) u := by
    intro i j
    have ha := hasSubst_pr (h0X (p := p) i) (h0X (p := p) j)
    rw [sub_pr hl0 (h0X i) (h0X j), hu]
    unfold pr
    rw [MvPowerSeries.subst_mul ha, MvPowerSeries.subst_sub ha, MvPowerSeries.subst_X ha,
      MvPowerSeries.subst_X ha]
    simp
  have hvS : ∀ i j : Fin 3, pr (MvPowerSeries.X i) (MvPowerSeries.X j) u ∈ SerS S (Fin 3) := fun i j =>
    pr_mem (h0X i) (h0X j) (X_mem_SerS' S i) (X_mem_SerS' S j) huS
  have hv1 : ∀ i j : Fin 3, MvPowerSeries.constantCoeff (pr (MvPowerSeries.X i) (MvPowerSeries.X j) u) = 1 :=
    fun i j => (cc_pr_eq (h0X i) (h0X j) u).trans hu0
  have hw1 : MvPowerSeries.constantCoeff (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u) = 1 := by
    rw [map_mul, map_mul, map_mul, hu11, hv1, hv1, hv1]
    norm_num
  have hwS : u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u * pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u *
      pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u ∈ SerS S (Fin 3) :=
    mul_mem (mul_mem (mul_mem hu1S (hvS 0 1)) (hvS 1 2)) (hvS 2 0)
  have hinv := MvPowerSeries.mul_inv_cancel (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u)
    (by rw [hw1]; exact one_ne_zero)
  refine ⟨m * (u1 * pr (MvPowerSeries.X 0) (MvPowerSeries.X 1) u *
      pr (MvPowerSeries.X 1) (MvPowerSeries.X 2) u * pr (MvPowerSeries.X 2) (MvPowerSeries.X 0) u)⁻¹,
    (hint _).2 (mul_mem hmS (PI.AddIntG.Wk.inv_mem_SerS S hw1 hwS)), ?_, ?_⟩
  · rw [map_mul, MvPowerSeries.constantCoeff_inv, hw1, hm1, inv_one, mul_one]
  · rw [T_eq, hμ, hmμ, hu1, hsub 0 1, hsub 1 2, hsub 2 0]
    linear_combination (-((MvPowerSeries.X 2 - s3 W wq) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
      (MvPowerSeries.X 1 - MvPowerSeries.X 2) * (MvPowerSeries.X 2 - MvPowerSeries.X 0) * m)) * hinv
end PI.FglTriFactor.Wk

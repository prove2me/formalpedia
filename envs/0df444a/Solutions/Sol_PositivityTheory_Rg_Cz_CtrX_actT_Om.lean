-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.actT_Om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:40:51.004997+00:00
-- url     : https://prove2.me/submissions/035f29c0-8e82-4928-b37e-7bceb6551a52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_sum
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_glue_j
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_update
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_prod
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one


section
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
private theorem Om_apply_eq_sum_update {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m)
    (g : TV n M (Fin m)) (I : Fin m → Fin n) :
    Om E j g I = ∑ a, E a (I j) (g (Function.update I j a)) := by
  simp only [Om, lift, eAt, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (I j)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h
private theorem actT_const_apply_eq_sum_prod_smul {ι Γ : Type} {m : ℕ} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (γ : Γ) (g : TV n M (Fin m)) (I : Fin m → Fin n) :
    actT (fun _ : Fin m => τ) κ ρ γ g I = ∑ J, (∏ p, κ τ γ (I p) (J p)) • ρ γ (g J) := by
  simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
private theorem sum_smul_R0_sum_E_eq_of_unitary_of_adjoint (K : Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M)
    (R0 : Module.End ℂ M) (hu : K * Kᴴ = 1)
    (had : ∀ a b, R0 * E a b = (∑ c, ∑ d, (K c a * star (K d b)) • E c d) * R0)
    (i : Fin n) (y : Fin n → M) :
    ∑ b, K i b • R0 (∑ a, E a b (y a)) = ∑ a, ∑ c, K c a • E c i (R0 (y a)) := by
  have h1 : ∀ a b, R0 (E a b (y a)) = ∑ c, ∑ d, (K c a * star (K d b)) • E c d (R0 (y a)) := by
    intro a b
    have h := congrArg (fun T : Module.End ℂ M => T (y a)) (had a b)
    simpa [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h
  have h2 : ∀ d, ∑ b, K i b * star (K d b) = if i = d then 1 else 0 := by
    intro d
    have h := congrFun (congrFun hu i) d
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.conjTranspose_apply] using h
  simp_rw [map_sum, h1, Finset.smul_sum, smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have h3 : ∀ d (v : M), ∑ b, (K i b * (K c a * star (K d b))) • v
      = (K c a * if i = d then 1 else 0) • v := by
    intro d v
    rw [← Finset.sum_smul, ← h2 d, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [h3]
  simp [mul_ite]
end PositivityTheory.Rg.Cz.CtrX
end
end

set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {ι Γ : Type} {m : ℕ} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M)
    (ρ : Γ → Module.End ℂ M) (γ : Γ) (hu : κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ a b, ρ γ * E a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E c d) * ρ γ) (j : Fin m)
    (f : TV n M (Fin m)) :
    actT (fun _ : Fin m => τ) κ ρ γ (Om E j f) = Om E j (actT (fun _ : Fin m => τ) κ ρ γ f) := by
  funext I
  rw [actT_const_apply_eq_sum_prod_smul, Om_apply_eq_sum_update]
  simp_rw [Om_apply_eq_sum_update, actT_const_apply_eq_sum_prod_smul]
  set K := κ τ γ with hK
  have hP : ∀ b R, ∏ p, K (I p) (omcGlue j b R p)
      = K (I j) b * ∏ p : {p // p ≠ j}, K (I p.1) (R p) :=
    fun b R => omc_prod j (fun p y => K (I p) y) b R
  have hQ : ∀ a b R, ∏ p, K (Function.update I j a p) (omcGlue j b R p)
      = K a b * ∏ p : {p // p ≠ j}, K (I p.1) (R p) := by
    intro a b R
    rw [show ∏ p, K (Function.update I j a p) (omcGlue j b R p)
        = K (Function.update I j a j) b * ∏ p : {p // p ≠ j}, K (Function.update I j a p.1) (R p)
        from omc_prod j (fun p y => K (Function.update I j a p) y) b R]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro p _
      rw [Function.update_of_ne p.2]
  trans ∑ R : {p // p ≠ j} → Fin n, (∏ p : {p // p ≠ j}, K (I p.1) (R p)) •
      ∑ a, ∑ c, K c a • E c (I j) (ρ γ (f (omcGlue j a R)))
  · conv_lhs => rw [omc_sum j]
    simp only [omc_glue_j, omc_update, hP]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [← sum_smul_R0_sum_E_eq_of_unitary_of_adjoint K E (ρ γ) hu had (I j) (fun a => f (omcGlue j a R)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, mul_comm]
  · have hR : ∀ a, E a (I j) (∑ J, (∏ p, K (Function.update I j a p) (J p)) • ρ γ (f J))
        = ∑ b, ∑ R, (K a b * ∏ p : {p // p ≠ j}, K (I p.1) (R p)) •
          E a (I j) (ρ γ (f (omcGlue j b R))) := by
      intro a
      rw [omc_sum j]
      simp only [hQ, map_sum, map_smul]
    simp only [hR]
    symm
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext b
      rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul, mul_comm]
end PositivityTheory.Rg.Cz.CtrX

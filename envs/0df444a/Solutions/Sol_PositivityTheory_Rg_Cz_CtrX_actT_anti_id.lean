-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.actT_anti_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:30:46.891026+00:00
-- url     : https://prove2.me/submissions/cec919b0-581e-4f26-9b01-34187212eb52

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_antisymmetric_eq_zero_of_not_injective
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



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {ι Γ : Type} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (f : TV n M (Fin n)) (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) :
    actT (fun _ : Fin n => τ) κ ρ γ f id = (κ τ γ).det • ρ γ (f id) := by
  set A := κ τ γ with hA
  have hsum : actT (fun _ : Fin n => τ) κ ρ γ f id
      = ∑ J : Fin n → Fin n, (∏ p, A p (J p)) • ρ γ (f J) := by
    simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, id, hA]
  have hperm : ∀ σ : Equiv.Perm (Fin n), f ⇑σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f id := by
    intro σ
    have h1 := congrFun (hf σ) id
    rw [Pi.smul_apply] at h1
    exact h1
  have hsub : ∑ J ∈ Finset.univ.image (fun σ : Equiv.Perm (Fin n) => (⇑σ : Fin n → Fin n)),
        (∏ p, A p (J p)) • ρ γ (f J)
      = ∑ J : Fin n → Fin n, (∏ p, A p (J p)) • ρ γ (f J) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro J _ hJ
    have hni : ¬ Function.Injective J := by
      intro hinj
      apply hJ
      rw [Finset.mem_image]
      exact ⟨Equiv.ofBijective J (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
    rw [antisymmetric_eq_zero_of_not_injective f hf J hni, map_zero, smul_zero]
  rw [hsum, ← hsub, Finset.sum_image (fun σ _ τ' _ h => Equiv.coe_fn_injective h)]
  simp_rw [hperm, map_smul, smul_smul]
  rw [← Finset.sum_smul, ← Matrix.det_transpose, Matrix.det_apply']
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_comm]
  rfl
end PositivityTheory.Rg.Cz.CtrX

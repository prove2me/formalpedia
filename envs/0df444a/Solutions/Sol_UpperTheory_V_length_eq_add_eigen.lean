-- Prove2me | solution 1 for UpperTheory.V.length_eq_add_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:07.017436+00:00
-- url     : https://prove2.me/submissions/77ae8c5e-bb65-4e73-a72a-7943eca8cf29

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.Top
open UpperTheory UpperTheory.V
namespace UpperTheory.V
theorem _root_.solution {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (h2 : IsUnit (2 : R))
    (N : Submodule R M) (f : Module.End R M) (hN : ∀ x ∈ N, f x ∈ N) (hf : ∀ x, f (f x) = x) (s : R) (hs : s * s = 1) :
    Module.length R N = Module.length R ↥(N ⊓ f.eigenspace s) + Module.length R ↥(N ⊓ f.eigenspace (-s)) := by
  set c : R := ↑h2.unit⁻¹ with hc_def
  have hc : (2 : R) * c = 1 := h2.mul_val_inv
  have eP : ∀ x : M, f (x + s • f x) = s • (x + s • f x) := by
    intro x
    rw [map_add, map_smul, hf, smul_add, smul_smul, hs, one_smul, add_comm]
  have eQ : ∀ x : M, f (x - s • f x) = (-s) • (x - s • f x) := by
    intro x
    rw [map_sub, map_smul, hf, smul_sub, smul_smul, neg_mul, hs, neg_smul, neg_smul, one_smul]
    abel
  have memP : ∀ x ∈ N, c • (x + s • f x) ∈ N ⊓ f.eigenspace s := fun x hx =>
    ⟨N.smul_mem c (N.add_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace s).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eP x))⟩
  have memQ : ∀ x ∈ N, c • (x - s • f x) ∈ N ⊓ f.eigenspace (-s) := fun x hx =>
    ⟨N.smul_mem c (N.sub_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace (-s)).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eQ x))⟩
  let toP : N →ₗ[R] ↥(N ⊓ f.eigenspace s) :=
    (c • (N.subtype + s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
        Submodule.coe_subtype]
      exact memP _ x.2)
  let toQ : N →ₗ[R] ↥(N ⊓ f.eigenspace (-s)) :=
    (c • (N.subtype - s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.coe_subtype]
      exact memQ _ x.2)
  let back : (↥(N ⊓ f.eigenspace s) × ↥(N ⊓ f.eigenspace (-s))) →ₗ[R] N :=
    (Submodule.inclusion inf_le_left).coprod (Submodule.inclusion inf_le_left)
  have h₁ : (toP.prod toQ) ∘ₗ back = LinearMap.id := by
    ext ⟨a, ha⟩
    all_goals simp [toP, toQ, back]
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
  have h₂ : back ∘ₗ (toP.prod toQ) = LinearMap.id := by
    ext ⟨x, hx⟩
    simp [toP, toQ, back]
    linear_combination (norm := module) hc • x
  rw [(LinearEquiv.ofLinear (toP.prod toQ) back h₁ h₂).length_eq, Module.length_prod]
end UpperTheory.V

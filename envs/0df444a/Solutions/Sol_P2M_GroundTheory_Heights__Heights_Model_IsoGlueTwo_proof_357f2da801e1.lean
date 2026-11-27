-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_proof_357f2da801e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:04:01.082222+00:00
-- url     : https://prove2.me/submissions/f45a9243-301d-4823-9374-ee77795936aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_homEquiv_pullbackIsoAlong_d3b70a0e6bc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_pullbackIsoAlong_symm_9ebafb92a361
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_hom_ext_b974d1ef1558
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_exists_hom_4266bc55ec24

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
namespace IsoGlueTwo
theorem _root_.solution : IsoGlueTwo.Statement := by
  intro Y P₁ P₂ P P₁₂ h₁ h₂ hP k₁ k₂ hk A B φ₁ φ₂ hφ
  have e₁ : Y.homOfLE k₁ ≫ Y.homOfLE h₁ = Y.homOfLE (k₁.trans h₁) := Y.homOfLE_homOfLE k₁ h₁
  have e₂ : Y.homOfLE k₂ ≫ Y.homOfLE h₂ = Y.homOfLE (k₁.trans h₁) := Y.homOfLE_homOfLE k₂ h₂
  have hφ' : pullbackIsoAlong e₁ φ₁ = pullbackIsoAlong e₂ φ₂ := hφ
  have hcov : ⊤ ≤ (Y.homOfLE h₁).opensRange ⊔ (Y.homOfLE h₂).opensRange := by
    rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.preimage_sup,
      ← P.ι_preimage_self]
    exact Scheme.Hom.preimage_mono _ hP
  have h₁₂ : ∀ O : (P : Scheme.{0}).Opens, O ≤ (Y.homOfLE h₁).opensRange →
      (Y.homOfLE h₂) ⁻¹ᵁ O ≤ (Y.homOfLE k₂).opensRange := by
    intro O hO
    rw [Scheme.opensRange_homOfLE] at hO ⊢
    refine (Scheme.Hom.preimage_mono _ hO).trans ?_
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
    intro x hx
    have hx2 : P₂.ι x ∈ P₂ := x.2
    exact hk ⟨hx, hx2⟩
  have h₂₁ : ∀ O : (P : Scheme.{0}).Opens, O ≤ (Y.homOfLE h₂).opensRange →
      (Y.homOfLE h₁) ⁻¹ᵁ O ≤ (Y.homOfLE k₁).opensRange := by
    intro O hO
    rw [Scheme.opensRange_homOfLE] at hO ⊢
    refine (Scheme.Hom.preimage_mono _ hO).trans ?_
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
    intro x hx
    have hx1 : P₁.ι x ∈ P₁ := x.2
    exact hk ⟨hx1, hx⟩
  have hhom := congrArg (fun ψ => (Scheme.Modules.pullbackPushforwardAdjunction
    (Y.homOfLE (k₁.trans h₁))).homEquiv _ _ ψ.hom) hφ'
  have hinv := congrArg (fun ψ => (Scheme.Modules.pullbackPushforwardAdjunction
    (Y.homOfLE (k₁.trans h₁))).homEquiv _ _ ψ.symm.hom) hφ'
  simp only [← IsoGlueTwo.pullbackIsoAlong_symm] at hinv
  simp only [IsoGlueTwo.homEquiv_pullbackIsoAlong] at hhom hinv
  obtain ⟨α, hα₁, hα₂⟩ := IsoGlueTwo.exists_hom _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ φ₁.hom φ₂.hom hhom
  obtain ⟨β, hβ₁, hβ₂⟩ := IsoGlueTwo.exists_hom _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ φ₁.inv φ₂.inv hinv
  refine ⟨⟨α, β, ?_, ?_⟩, ?_, ?_⟩
  · apply IsoGlueTwo.hom_ext _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ <;> simp [hα₁, hα₂, hβ₁, hβ₂]
  · apply IsoGlueTwo.hom_ext _ _ _ _ e₁ e₂ hcov h₁₂ h₂₁ <;> simp [hα₁, hα₂, hβ₁, hβ₂]
  · ext1; exact hα₁
  · ext1; exact hα₂
end IsoGlueTwo
end GroundTheory.Heights₂.Heights.Model

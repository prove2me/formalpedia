-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_exists_hom_4266bc55ec24
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:07.412483+00:00
-- url     : https://prove2.me/submissions/55b99edd-14fe-4edc-a0c8-6c39e6d55b9a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_comp_unit_52fb082bdcf8

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
open GroundTheory.Heights₂.Heights.Model.IsoGlueTwo
open Scheme.Modules GlueModulesStar
variable {X Z₁ Z₂ T : Scheme.{0}}
variable (f₁ : Z₁ ⟶ X) (f₂ : Z₂ ⟶ X) [IsOpenImmersion f₁] [IsOpenImmersion f₂]
  (g₁ : T ⟶ Z₁) (g₂ : T ⟶ Z₂) [IsOpenImmersion g₁] [IsOpenImmersion g₂] {k : T ⟶ X}
  (e₁ : g₁ ≫ f₁ = k) (e₂ : g₂ ≫ f₂ = k)
namespace GroundTheory.Heights₂.Heights.Model.IsoGlueTwo
theorem _root_.solution (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) {A B : X.Modules}
    (φ₁ : (Scheme.Modules.pullback f₁).obj A ⟶ (Scheme.Modules.pullback f₁).obj B)
    (φ₂ : (Scheme.Modules.pullback f₂).obj A ⟶ (Scheme.Modules.pullback f₂).obj B)
    (h : (pullbackPushforwardAdjunction f₁).homEquiv _ _ φ₁ ≫ restrictOverlap g₁ f₁ e₁ B =
      (pullbackPushforwardAdjunction f₂).homEquiv _ _ φ₂ ≫ restrictOverlap g₂ f₂ e₂ B) :
    ∃ α : A ⟶ B, (Scheme.Modules.pullback f₁).map α = φ₁ ∧
      (Scheme.Modules.pullback f₂).map α = φ₂ := by
  have l := isLimit f₁ f₂ g₁ g₂ e₁ e₂ hcov h₁₂ h₂₁ B
  refine ⟨PullbackCone.IsLimit.lift l _ _ h, ?_, ?_⟩
  · apply ((pullbackPushforwardAdjunction f₁).homEquiv _ _).injective
    exact (comp_unit f₁ _).symm.trans (PullbackCone.IsLimit.lift_fst l _ _ h)
  · apply ((pullbackPushforwardAdjunction f₂).homEquiv _ _).injective
    exact (comp_unit f₂ _).symm.trans (PullbackCone.IsLimit.lift_snd l _ _ h)
end GroundTheory.Heights₂.Heights.Model.IsoGlueTwo

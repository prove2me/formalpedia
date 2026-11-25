-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_hom_ext_b974d1ef1558
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:08.659545+00:00
-- url     : https://prove2.me/submissions/1668a08d-13a7-401c-b067-0494ca14b59f

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
include e₁ e₂
namespace GroundTheory.Heights₂.Heights.Model.IsoGlueTwo
theorem _root_.solution (hcov : ⊤ ≤ f₁.opensRange ⊔ f₂.opensRange)
    (h₁₂ : ∀ O : X.Opens, O ≤ f₁.opensRange → f₂ ⁻¹ᵁ O ≤ g₂.opensRange)
    (h₂₁ : ∀ O : X.Opens, O ≤ f₂.opensRange → f₁ ⁻¹ᵁ O ≤ g₁.opensRange) {A B : X.Modules} (α β : A ⟶ B)
    (h₁ : (Scheme.Modules.pullback f₁).map α = (Scheme.Modules.pullback f₁).map β)
    (h₂ : (Scheme.Modules.pullback f₂).map α = (Scheme.Modules.pullback f₂).map β) : α = β := by
  apply PullbackCone.IsLimit.hom_ext (isLimit f₁ f₂ g₁ g₂ e₁ e₂ hcov h₁₂ h₂₁ B)
  · exact (comp_unit f₁ α).trans ((congrArg _ h₁).trans (comp_unit f₁ β).symm)
  · exact (comp_unit f₂ α).trans ((congrArg _ h₂).trans (comp_unit f₂ β).symm)
end GroundTheory.Heights₂.Heights.Model.IsoGlueTwo

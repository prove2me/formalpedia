-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_comp_unit_52fb082bdcf8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:00.359221+00:00
-- url     : https://prove2.me/submissions/90db27da-b39e-4205-8fe8-d8b78016bd38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo

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
theorem _root_.solution {Z : Scheme.{0}} (f : Z ⟶ X) {A B : X.Modules} (α : A ⟶ B) :
    α ≫ (pullbackPushforwardAdjunction f).unit.app B =
      (pullbackPushforwardAdjunction f).homEquiv _ _ ((Scheme.Modules.pullback f).map α) := by
  rw [Adjunction.homEquiv_unit, Adjunction.unit_naturality]
end GroundTheory.Heights₂.Heights.Model.IsoGlueTwo

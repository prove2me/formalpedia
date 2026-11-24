-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_unit_app_52e1385b04f1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:46.527803+00:00
-- url     : https://prove2.me/submissions/9081d66c-e25e-4640-b77f-903e6f7d3c90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar

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
open GroundTheory.Heights₂.Heights.Model.GlueModulesStar
universe u
set_option backward.isDefEq.respectTransparency false
open Scheme.Modules
namespace GroundTheory.Heights₂.Heights.Model.GlueModulesStar
theorem _root_.solution {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] (M : Z.Modules)
    (O : Z.Opens) (hO : O ≤ f.opensRange) :
    IsIso (((pullbackPushforwardAdjunction f).unit.app M).app O) := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
    (pullbackPushforwardAdjunction f) M, Hom.comp_app, restrictAdjunction_unit_app_app,
    pushforward_map_app]
  have h1 : f ''ᵁ f ⁻¹ᵁ O = O := by
    rw [f.image_preimage_eq_opensRange_inf]; exact inf_eq_right.mpr hO
  have : IsIso (homOfLE (f.image_preimage_le O)) :=
    ⟨⟨homOfLE h1.ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  have : IsIso (((restrictAdjunction f).leftAdjointUniq
      (pullbackPushforwardAdjunction f)).hom.app M) := inferInstance
  exact IsIso.comp_isIso' inferInstance inferInstance
end GroundTheory.Heights₂.Heights.Model.GlueModulesStar

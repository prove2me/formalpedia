-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_homEquiv_symm_a5562e9ab15b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:46.031803+00:00
-- url     : https://prove2.me/submissions/cb65e37d-00b3-42f9-9de5-e2e758261e89

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
open Scheme.Modules
namespace GroundTheory.Heights₂.Heights.Model.GlueModulesStar
theorem _root_.solution {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] {E : Z.Modules}
    {M : Y.Modules} (φ : E ⟶ (pushforward f).obj M) (h : ∀ O : Y.Opens, IsIso (φ.app (f ''ᵁ O))) :
    IsIso (((pullbackPushforwardAdjunction f).homEquiv _ _).symm φ) := by
  have key : ((pullbackPushforwardAdjunction f).homEquiv _ _).symm φ =
      (restrictFunctorIsoPullback f).inv.app E ≫ (restrictFunctor f).map φ ≫
        (restrictAdjunction f).counit.app M := by
    rw [Adjunction.homEquiv_counit, ← Adjunction.leftAdjointUniq_hom_app_counit
      (restrictAdjunction f) (pullbackPushforwardAdjunction f) M, restrictFunctorIsoPullback]
    simp only [NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]
  have : IsIso ((restrictFunctor f).map φ) := by
    rw [Hom.isIso_iff_isIso_app]
    intro O
    exact h O
  rw [key]
  infer_instance
end GroundTheory.Heights₂.Heights.Model.GlueModulesStar

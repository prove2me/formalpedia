-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_homEquiv_pullbackIsoAlong_d3b70a0e6bc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:57.996904+00:00
-- url     : https://prove2.me/submissions/eebca8c9-ba91-452d-8193-65bb77737afc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsIsoGlueTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PIsoGlueTwo
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_transMap_pullback_map_afc42c0b28e0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_homEquiv_pullbackCompIso_3c20fd696aa0


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
namespace GroundTheory.Heights₂.Heights.Model.IsoGlueTwo
theorem _root_.solution (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {A B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) :
    (pullbackPushforwardAdjunction k).homEquiv _ _ (pullbackIsoAlong e φ).hom =
      (pullbackPushforwardAdjunction f).homEquiv _ _ φ.hom ≫ restrictOverlap g f e B := by
  have h := homEquiv_pullbackCompIso e (Iso.refl ((Scheme.Modules.pullback f).obj A))
    ((Scheme.Modules.pullback g).map φ.hom ≫ (pullbackCompIso e (Iso.refl _)).inv)
  have h2 : (pullbackPushforwardAdjunction f).homEquiv _ _ (𝟙 _) ≫ (pushforward f).map φ.hom =
      (pullbackPushforwardAdjunction f).homEquiv _ _ φ.hom := by
    rw [← Adjunction.homEquiv_naturality_right, Category.id_comp]
  rw [transMap_pullback_map, Iso.refl_hom] at h
  rw [restrictOverlap, ← h2, Category.assoc, ← h]
  simp only [pullbackIsoAlong, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
end GroundTheory.Heights₂.Heights.Model.IsoGlueTwo

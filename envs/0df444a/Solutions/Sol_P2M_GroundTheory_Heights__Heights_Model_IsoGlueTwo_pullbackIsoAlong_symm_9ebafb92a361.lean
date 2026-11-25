-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_pullbackIsoAlong_symm_9ebafb92a361
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:04:36.407493+00:00
-- url     : https://prove2.me/submissions/aff4e672-de8d-412c-8077-5fda9752b063

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
namespace GroundTheory.Heights₂.Heights.Model.IsoGlueTwo
theorem _root_.solution (g : T ⟶ Z₁) (f : Z₁ ⟶ X) {k : T ⟶ X} (e : g ≫ f = k)
    {A B : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj A ≅ (Scheme.Modules.pullback f).obj B) :
    pullbackIsoAlong e φ.symm = (pullbackIsoAlong e φ).symm := by
  ext1
  simp only [pullbackIsoAlong, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
end GroundTheory.Heights₂.Heights.Model.IsoGlueTwo

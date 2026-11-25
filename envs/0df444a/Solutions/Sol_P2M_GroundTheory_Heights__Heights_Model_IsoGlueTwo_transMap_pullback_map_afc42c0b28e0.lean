-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsoGlueTwo_transMap_pullback_map_afc42c0b28e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:00.805835+00:00
-- url     : https://prove2.me/submissions/86c384be-ed22-43ba-bd86-2bfadd6f87fa

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
    {M M' : Z₁.Modules} {N : T.Modules} (a : M ⟶ M') (χ : (Scheme.Modules.pullback g).obj M' ⟶ N) :
    transMap g f e ((Scheme.Modules.pullback g).map a ≫ χ) = (pushforward f).map a ≫ transMap g f e χ := by
  simp only [transMap, Adjunction.homEquiv_naturality_left, Functor.map_comp, Category.assoc]
end GroundTheory.Heights₂.Heights.Model.IsoGlueTwo

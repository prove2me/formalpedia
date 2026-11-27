-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PrimitiveFormSheetedOffDiscriminant_proof_8d087ee50edf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:59:31.595958+00:00
-- url     : https://prove2.me/submissions/859e6630-4613-488c-8a95-ac0ea3d77ed0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedLocusCutOut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedPointsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormSheetedOffDiscriminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace PrimitiveFormSheetedOffDiscriminant
theorem _root_.solution (hcut : PrimitiveFormSheetedLocusCutOut.Statement)
    (hnear : PrimitiveFormSheetedPointsNear.Statement) : PrimitiveFormSheetedOffDiscriminant.Statement := by
  intro σ _ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨c, e, hc, he, hce, hsh⟩ := hcut σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  rcases hirr.2 c e hc he hce with hc0 | he0
  · exact ⟨_, hc0.and hsh, fun y hy hyδ => ((hy.2.2 hy.1 hyδ).1).2 (hy.2.1 hy.1)⟩
  · exfalso
    obtain ⟨z, hz, hzδ, hzs⟩ :=
      hnear σ X w d A hX hirr hiso hinj ℓ N a δ q ha hδ hq hδ0 hP hsep hQ _ (he0.and hsh)
    exact (hz.2.2 hz.1 hzδ).2 hzs (hz.2.1 hz.1)
end PrimitiveFormSheetedOffDiscriminant
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

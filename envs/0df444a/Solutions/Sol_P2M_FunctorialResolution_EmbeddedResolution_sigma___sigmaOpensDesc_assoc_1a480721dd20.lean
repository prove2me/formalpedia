-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_assoc_1a480721dd20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:49:04.031093+00:00
-- url     : https://prove2.me/submissions/1052cdd3-d0e7-47b9-835c-0632d6f0c2e1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens) (i : ι)
    {Z : Scheme.{u}} (h : Y ⟶ Z) :
    Sigma.ι (fun i => (U i).toScheme) i ≫ sigmaOpensDesc Y U ≫ h = (U i).ι ≫ h := by
  simp
end FunctorialResolution.EmbeddedResolution

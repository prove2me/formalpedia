-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isInducing_subscheme__comp___cc236b5b1af5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:31.913681+00:00
-- url     : https://prove2.me/submissions/a5551f32-e221-40b9-a50c-77e0ff42553f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (W : Scheme.{u}) (U : W.Opens) (D : (U.toScheme).IdealSheafData) :
    Topology.IsInducing ⇑(D.subschemeι ≫ U.ι).base := by
  have h1 : Topology.IsInducing ⇑D.subschemeι.base :=
    (hV.isClosedEmbedding_subschemeι U.toScheme D).toIsEmbedding.toIsInducing
  have h2 : Topology.IsInducing ⇑U.ι.base := (hV.isEmbedding_ι W U).toIsInducing
  have hfun : ⇑(D.subschemeι ≫ U.ι).base = ⇑U.ι.base ∘ ⇑D.subschemeι.base := by
    funext y
    exact hV.base_comp _ _ _ D.subschemeι U.ι y
  rw [hfun]
  exact h2.comp h1
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

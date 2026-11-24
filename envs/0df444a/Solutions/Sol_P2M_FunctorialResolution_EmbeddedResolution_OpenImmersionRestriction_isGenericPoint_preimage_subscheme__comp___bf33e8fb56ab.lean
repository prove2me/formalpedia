-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isGenericPoint_preimage_subscheme__comp___bf33e8fb56ab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:52.723859+00:00
-- url     : https://prove2.me/submissions/bb0c1f82-f0e7-4a71-9f83-5f1f6abae661

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_isInducing_subscheme__comp___cc236b5b1af5
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isGenericPoint_preimage_of_isInducing


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
    (W : Scheme.{u}) (U : W.Opens) (D : (U.toScheme).IdealSheafData) (T : Set ↥W)
    (ξ : ↥W) (hξ : IsGenericPoint ξ T) (y : ↥(D.subscheme))
    (hy : (D.subschemeι ≫ U.ι).base y = ξ) :
    IsGenericPoint y ((D.subschemeι ≫ U.ι).base ⁻¹' T) :=
  isGenericPoint_preimage_of_isInducing (isInducing_subschemeι_comp_ι hV W U D) hξ hy
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_orderAt_comap___3b37585930bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:15:44.593357+00:00
-- url     : https://prove2.me/submissions/c8b52e3a-8515-484b-b222-cfcf4ba99e8c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_comap_of_isOpenImmersion


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
theorem _root_.solution (W : Scheme.{u}) (V : W.Opens) (I : W.IdealSheafData)
    (y : ↥(V.toScheme)) :
    orderAt (I.comap V.ι) y = orderAt I (V.ι.base y) :=
  FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion V.ι I y
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

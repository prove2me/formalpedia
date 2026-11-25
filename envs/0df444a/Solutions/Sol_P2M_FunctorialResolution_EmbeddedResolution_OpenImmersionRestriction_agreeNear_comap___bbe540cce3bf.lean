-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_comap___bbe540cce3bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:48:50.532151+00:00
-- url     : https://prove2.me/submissions/396b0c6e-2d8e-4cb9-917d-5e7c6b20a00e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_agreeNear_iff


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
theorem _root_.solution (W : Scheme.{u}) (V : W.Opens) (I J : W.IdealSheafData)
    (y : ↥(V.toScheme)) (h : AgreeNear I J (V.ι.base y)) :
    AgreeNear (I.comap V.ι) (J.comap V.ι) y := by
  obtain ⟨U, hU, hEq⟩ := (agreeNear_iff I J (V.ι.base y)).mp h
  refine (agreeNear_iff _ _ _).mpr ⟨V.ι ⁻¹ᵁ U, hU, ?_⟩
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ← morphismRestrict_ι V.ι U, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_comp, hEq]
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

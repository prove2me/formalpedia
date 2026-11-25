-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_hasStrictNormalCrossingsWith_224aeeb9bb66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:28:52.538654+00:00
-- url     : https://prove2.me/submissions/e341658f-1d65-4e06-ae54-bab120f09152

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_AffineSpaceSmooth
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_smooth_subscheme__comp_of_locally_eq_coordIdeal_58ee398429d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Z : X.IdealSheafData) (E : List X.IdealSheafData)
    (h : HasStrictNormalCrossingsWith p Z E) : Smooth (Z.subschemeι ≫ p) := by
  unfold HasStrictNormalCrossingsWith at h
  refine smooth_subschemeι_comp_of_locally_eq_coordIdeal Z ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, S, -, -, -, hS⟩ := h x hx
  exact ⟨U, hxU, n, c, S, hS⟩
end FunctorialResolution.EmbeddedResolution

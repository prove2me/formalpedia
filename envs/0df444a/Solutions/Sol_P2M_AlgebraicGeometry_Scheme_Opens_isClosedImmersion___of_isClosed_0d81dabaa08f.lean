-- Prove2me | solution 1 for P2M_AlgebraicGeometry_Scheme_Opens_isClosedImmersion___of_isClosed_0d81dabaa08f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:49.792677+00:00
-- url     : https://prove2.me/submissions/7a1211d5-11ff-485d-9ec7-68f8b923da7c

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_ClopenSubscheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Opens
namespace AlgebraicGeometry.Scheme.Opens
theorem _root_.solution {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion U.ι (by rw [U.range_ι]; exact hU)
end AlgebraicGeometry.Scheme.Opens

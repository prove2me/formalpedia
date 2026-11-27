-- Prove2me | solution 1 for P2M_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_comap_subscheme__eraseIdx_of_eq_4a34b7aecc30
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:51:02.701959+00:00
-- url     : https://prove2.me/submissions/853adba7-dda2-4bd8-a3c7-ac6cbd49cd8a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_StrictNormalCrossingsEraseMember
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_inStrictNormalCrossingPosition_comap_subscheme__eraseIdx_dbcc62aebfa3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) (D : X.IdealSheafData) (hD : E[j]'hj = D) :
    InStrictNormalCrossingPosition (D.subschemeι ≫ p)
      ((E.eraseIdx j).map fun F => F.comap D.subschemeι) := by
  subst hD
  exact inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx p E hE j hj
end FunctorialResolution.EmbeddedResolution

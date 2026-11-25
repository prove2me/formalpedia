-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IndependenceOfSmoothMetric_of_indep_d56dd1840959
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:32:10.226481+00:00
-- url     : https://prove2.me/submissions/b3bf033d-ef3a-4ecd-ac2c-a4fc669ac6db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace IndependenceOfSmoothMetric
theorem _root_.solution (h : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement) :
    IndependenceOfSmoothMetric.Statement :=
  fun K _ ι _ I P A s t hP _ hs ht => h K ι I P A s t hP hs ht
end IndependenceOfSmoothMetric
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

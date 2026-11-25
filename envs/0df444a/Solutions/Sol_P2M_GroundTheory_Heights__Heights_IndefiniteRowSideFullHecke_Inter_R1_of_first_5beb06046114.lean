-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_R1_of_first_5beb06046114
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:57.81329+00:00
-- url     : https://prove2.me/submissions/cc8da746-ca23-462a-a694-6ce96d27249f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_IndependenceOfSmoothMetric_of_indep_d56dd1840959
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_R1_equiv_smooth_0fb3f1843f02

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
namespace R1
theorem _root_.solution
    (h : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement ∧ GroundTheory.Heights₂.Heights.Inter.RegularityAdditive.Statement) :
    R1.Statement :=
  R1.equiv_smooth.mp ⟨IndependenceOfSmoothMetric.of_indep h.1, h.2⟩
end R1
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

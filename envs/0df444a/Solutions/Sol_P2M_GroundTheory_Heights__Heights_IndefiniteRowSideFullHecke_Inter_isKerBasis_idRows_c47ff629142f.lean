-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isKerBasis_idRows_c47ff629142f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:33.700177+00:00
-- url     : https://prove2.me/submissions/eb8abd85-10a2-4371-acd4-74daa018691b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution (n : ℕ) : IsKerBasis (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows n) (idRows n) := by
  refine ⟨(Pi.basisFun _ _).linearIndependent, ?_⟩
  rw [idRows, (Pi.basisFun _ _).span_eq]
  symm
  rw [LinearMap.ker_eq_top]
  exact LinearMap.ext fun _ => Subsingleton.elim _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

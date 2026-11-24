-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_isQuotRows_noRows_069a8b58390d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:34.614479+00:00
-- url     : https://prove2.me/submissions/8a1645f0-a955-40c6-84f9-3b82e44bbde2

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
theorem _root_.solution (n : ℕ) : IsQuotRows (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows n) 0 n := by
  refine ⟨fun a => a.elim0, fun F _ x _ => ?_⟩
  rw [Subsingleton.elim (Matrix.of fun a j => evalAt x (noRows n a j)) 0, Matrix.rank_zero, zero_add]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

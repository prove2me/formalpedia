-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_sq_4c51336df9f8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:53.930483+00:00
-- url     : https://prove2.me/submissions/634f3d64-505f-43e1-91ec-1ef304ff6033

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_inner_pairPt_67e7c5e8e409

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.AreaGraphPiece
variable {k m : ℕ}
namespace GroundTheory.Heights₂.Heights.AreaGraphPiece
theorem _root_.solution (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt u w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_pairPt]
end GroundTheory.Heights₂.Heights.AreaGraphPiece

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_zero_be1159debaaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:37.561865+00:00
-- url     : https://prove2.me/submissions/bea7d764-b971-46c1-a3d6-e1733f9c7a3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_pairPt_sq_4c51336df9f8

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
theorem _root_.solution (w : EuclideanSpace ℝ (Fin m)) :
    ‖pairPt (0 : EuclideanSpace ℝ (Fin k)) w‖ = ‖w‖ := by
  have h := norm_pairPt_sq (0 : EuclideanSpace ℝ (Fin k)) w
  rw [norm_zero, zero_pow two_ne_zero, zero_add] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h
end GroundTheory.Heights₂.Heights.AreaGraphPiece

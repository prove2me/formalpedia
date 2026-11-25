-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphPiece_pairPt_sub_f54c10fbd1af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:39.070528+00:00
-- url     : https://prove2.me/submissions/cc47f2a1-498e-433e-9dc2-21c9f97e78db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece

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
theorem _root_.solution (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w - pairPt u' w' = pairPt (u - u') (w - w') := by
  ext i
  rcases i with i | i <;> simp [pairPt]
end GroundTheory.Heights₂.Heights.AreaGraphPiece

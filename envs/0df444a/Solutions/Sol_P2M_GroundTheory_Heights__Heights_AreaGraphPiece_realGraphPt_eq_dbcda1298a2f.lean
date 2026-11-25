-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphPiece_realGraphPt_eq_dbcda1298a2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:32.32783+00:00
-- url     : https://prove2.me/submissions/1ca48d9a-feb6-46dc-bfac-003c0a7e1f48

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
theorem _root_.solution (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : realGraphPt F x = pairPt x (F x) := rfl
end GroundTheory.Heights₂.Heights.AreaGraphPiece

-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_realGraphPt_continuousOn_acf3943910ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:21.065164+00:00
-- url     : https://prove2.me/submissions/85493155-e0cc-4b31-8881-2676e562afea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound

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
open MeasureTheory
open scoped ENNReal NNReal
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {k m : ℕ} {F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin k))} (hF : ContinuousOn F s) : ContinuousOn (realGraphPt F) s := by
  unfold realGraphPt
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i => ?_)
  rcases i with i | i
  · exact (PiLp.continuous_apply 2 _ i).continuousOn
  · exact (PiLp.continuous_apply 2 _ i).comp_continuousOn hF
end GroundTheory.Heights₂.Heights

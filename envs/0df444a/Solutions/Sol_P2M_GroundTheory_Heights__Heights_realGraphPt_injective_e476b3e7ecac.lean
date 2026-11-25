-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_realGraphPt_injective_e476b3e7ecac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:25.253636+00:00
-- url     : https://prove2.me/submissions/dfe0713c-8bb8-4361-96ca-2b171b2f5823

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
theorem _root_.solution {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)) :
    Function.Injective (realGraphPt F) := by
  intro x y hxy
  ext i
  simpa [realGraphPt] using congrArg (fun z : EuclideanSpace ℝ (Fin k ⊕ Fin m) => z (Sum.inl i)) hxy
end GroundTheory.Heights₂.Heights

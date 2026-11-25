-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphPiece_normDet_graphLin_eb5fb2a3868a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:51.441187+00:00
-- url     : https://prove2.me/submissions/f3a40f8e-72a1-4538-ab75-07df45ed6777

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_adjoint_graphLin_comp_1b8b5de698b2

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
theorem _root_.solution (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    (graphLin A).normDet =
      graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  unfold graphJac
  rw [← adjoint_graphLin_comp, ← LinearMap.normDet_sq (graphLin A)]
  push_cast
  exact (Real.sqrt_sq (LinearMap.normDet_nonneg _)).symm
end GroundTheory.Heights₂.Heights.AreaGraphPiece

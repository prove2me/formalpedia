-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AreaGraphPiece_adjoint_graphLin_comp_1b8b5de698b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:32.420602+00:00
-- url     : https://prove2.me/submissions/4b5fa60e-af32-449b-9fd0-5e09bba586f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_inner_pairPt_67e7c5e8e409
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_graphLin_apply_abc67cdea5c9

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
    LinearMap.adjoint (graphLin A) ∘ₗ graphLin A =
      (1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
        LinearMap.adjoint (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∘ₗ
          (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.add_apply, inner_add_left,
    Module.End.one_apply, LinearMap.comp_apply, LinearMap.adjoint_inner_left, graphLin_apply,
    graphLin_apply, inner_pairPt]
  rfl
end GroundTheory.Heights₂.Heights.AreaGraphPiece

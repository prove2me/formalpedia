-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KShort_finite_ball_944d5e9d2efe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:36.290903+00:00
-- url     : https://prove2.me/submissions/ad2f1c5a-60b8-4ac4-b3cd-37705260f922

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ShortVectors

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
open MeasureTheory Module Metric
noncomputable section
open GroundTheory.Heights₂.Heights.KShort
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.KShort
theorem _root_.solution (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] (r : ℝ) :
    {v | v ∈ L ∧ ‖v‖ ≤ r}.Finite := by
  have h := Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
    (s := (L : Set (EuclideanSpace ℝ (Fin n)))) DiscreteTopology.isDiscrete isBounded_closedBall
    (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete)
  refine h.subset ?_
  rintro v ⟨hv, hr⟩
  exact ⟨by simpa using hr, hv⟩
end GroundTheory.Heights₂.Heights.KShort

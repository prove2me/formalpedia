-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MinkowskiCount_finite_latticePoints_4885546fbfad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:35.512081+00:00
-- url     : https://prove2.me/submissions/f3f2b088-05be-4ee2-8a2d-e5a620125c18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMinkowskiCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Module Metric
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount
theorem _root_.solution (La : Submodule ℤ V) [DiscreteTopology La] (ρ : ℝ) :
    {x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.Finite := by
  have h : {x : V | x ∈ La ∧ ‖x‖ ≤ ρ} = closedBall 0 ρ ∩ (La : Set V) := by
    ext x; simp [and_comm]
  rw [h]
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete
end GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount

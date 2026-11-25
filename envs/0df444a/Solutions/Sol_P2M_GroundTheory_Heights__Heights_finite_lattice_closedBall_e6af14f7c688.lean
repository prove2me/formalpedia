-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finite_lattice_closedBall_e6af14f7c688
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:58:03.221398+00:00
-- url     : https://prove2.me/submissions/4ff7a319-b4e6-4f21-82f8-944fafd719eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module ZSpan NumberField
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L]
omit [MeasurableSpace V] [BorelSpace V]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (r : ℝ) : {x : V | x ∈ L ∧ ‖x‖ ≤ r}.Finite := by
  have h := Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : V) r)
    (s := (L : Set V)) DiscreteTopology.isDiscrete isBounded_closedBall
    (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete)
  refine h.subset ?_
  rintro v ⟨hv, hr⟩
  exact ⟨by simpa using hr, hv⟩
end GroundTheory.Heights₂.Heights

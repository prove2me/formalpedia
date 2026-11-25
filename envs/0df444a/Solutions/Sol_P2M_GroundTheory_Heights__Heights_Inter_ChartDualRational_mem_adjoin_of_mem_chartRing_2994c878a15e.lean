-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_mem_adjoin_of_mem_chartRing_2994c878a15e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:29.395797+00:00
-- url     : https://prove2.me/submissions/0e0dc6e4-bf0f-409c-9d17-5ec0009ed8dc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDualRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDualRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter.ChartDualRational
variable {Ω : Type*} [Field Ω] {R : Subalgebra ℤ Ω}
namespace GroundTheory.Heights₂.Heights.Inter.ChartDualRational
theorem _root_.solution [CharZero Ω] {ι : Type*} (x : ι → Ω) (i : ι) {a : Ω} (ha : a ∈ chartRing ℤ x i) :
    a ∈ IntermediateField.adjoin ℚ (Set.range fun j ↦ x j / x i) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
  | algebraMap r => simp
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz
end GroundTheory.Heights₂.Heights.Inter.ChartDualRational

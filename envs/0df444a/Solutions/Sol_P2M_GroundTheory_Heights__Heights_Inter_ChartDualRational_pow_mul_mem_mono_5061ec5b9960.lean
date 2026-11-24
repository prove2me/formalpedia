-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartDualRational_pow_mul_mem_mono_5061ec5b9960
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:47.331292+00:00
-- url     : https://prove2.me/submissions/ae4281d2-50ba-4cb8-b514-b262e9304fb9

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
theorem _root_.solution {u y : Ω} (hu : u ∈ R) {n m : ℕ} (hnm : n ≤ m) (h : u ^ n * y ∈ R) :
    u ^ m * y ∈ R := by
  rw [← pow_mul_pow_sub u hnm, mul_comm (u ^ n), mul_assoc]
  exact mul_mem (pow_mem hu _) h
end GroundTheory.Heights₂.Heights.Inter.ChartDualRational

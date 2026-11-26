-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_subset_closedBall_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:38:08.166482+00:00
-- url     : https://prove2.me/submissions/748f1641-77ef-458c-b38d-be78480707c0

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) :
    centeredNumericalRadiusMinimizers A ⊆
      Metric.closedBall 0 (2 * numericalRadius A) := by
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_two_mul_numericalRadius_of_mem_centeredMinimizers A hc

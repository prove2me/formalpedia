-- Prove2me | solution 1 for abs_numericalRadius_sub_smul_one_sub_numericalRadius_sub_smul_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:46.313694+00:00
-- url     : https://prove2.me/submissions/16fe6116-9a84-4d83-85c7-e95d588783e5

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_abs_numericalRadius_sub_le_norm


set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c d : ℂ) :
    |numericalRadius (A - c • 1) - numericalRadius (A - d • 1)| ≤ ‖c - d‖ := by
  have h := abs_numericalRadius_sub_le_norm (A - c • 1) (A - d • 1)
  have hop : (A - c • 1) - (A - d • 1) = (d - c) • 1 := by
    module
  rw [hop, norm_smul, norm_one, mul_one, norm_sub_rev] at h
  exact h

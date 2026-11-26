-- Prove2me | solution 1 for abs_numericalRadius_add_smul_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:31.32112+00:00
-- url     : https://prove2.me/submissions/c27a8666-5d35-4e0d-bbc4-6b064b7bdc8f

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_numericalRadius_one
import Theorems.Thm_numericalRadius_smul_one
import Theorems.Thm_abs_numericalRadius_sub_le_norm
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRange_scalar
import Theorems.Thm_numericalRange_zero
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_adjoint
attribute [local simp] numericalRadius_neg
attribute [local simp] numericalRange_scalar
attribute [local simp] numericalRange_zero


attribute [local simp] numericalRadius_one
attribute [local simp] numericalRadius_smul_one

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    |numericalRadius (A + c • 1) - numericalRadius A| ≤ ‖c‖ := by
  have h := abs_numericalRadius_sub_le_norm (A + c • 1) A
  simpa only [add_sub_cancel_left, norm_smul, norm_one, mul_one] using h

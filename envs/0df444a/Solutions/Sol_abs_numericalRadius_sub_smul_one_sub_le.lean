-- Prove2me | solution 1 for abs_numericalRadius_sub_smul_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:45.714287+00:00
-- url     : https://prove2.me/submissions/f4613341-6b05-4c34-8c41-95674990d8ea

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_numericalRadius_one
import Theorems.Thm_numericalRadius_smul_one
import Theorems.Thm_abs_numericalRadius_add_smul_one_sub_le
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
    |numericalRadius (A - c • 1) - numericalRadius A| ≤ ‖c‖ := by
  simpa only [sub_eq_add_neg, neg_smul, norm_neg] using
    abs_numericalRadius_add_smul_one_sub_le A (-c)

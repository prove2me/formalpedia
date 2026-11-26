-- Prove2me | solution 1 for abs_numericalRadius_sub_smul_one_sub_norm_le_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:31.971872+00:00
-- url     : https://prove2.me/submissions/69b9bd6e-de99-48f0-a61c-26cd120d406e

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_numericalRadius_smul_one
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRadius_sub_le
import Theorems.Thm_numericalRange_scalar
import Theorems.Thm_numericalRange_zero
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_adjoint
attribute [local simp] numericalRadius_neg
attribute [local simp] numericalRange_scalar
attribute [local simp] numericalRange_zero


attribute [local simp] numericalRadius_smul_one

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    |numericalRadius (A - c • 1) - ‖c‖| ≤ numericalRadius A := by
  rw [abs_le]
  constructor
  · have h := numericalRadius_sub_le A (A - c • 1)
    have hop : A - (A - c • 1) = c • 1 := by module
    rw [hop, numericalRadius_smul_one] at h
    linarith
  · have h := numericalRadius_sub_le A (c • 1)
    rw [numericalRadius_smul_one] at h
    linarith

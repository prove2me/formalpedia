-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:12:19.911653+00:00
-- url     : https://prove2.me/submissions/72bb4b77-007d-4f87-8af5-4d9f5762d2b4

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_numericalRadius_one
import Theorems.Thm_numericalRadius_smul_one
import Theorems.Thm_centeredNumericalRadiusMinimizers_neg
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRadius_nonneg
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
attribute [local simp] centeredNumericalRadiusMinimizers_neg

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution :
    centeredNumericalRadiusMinimizers (0 : E →L[ℂ] E) = {0} := by
  ext c
  rw [Set.mem_singleton_iff]
  constructor
  · intro hc
    have h := hc 0
    have hc0 : ‖c‖ ≤ 0 := by
      simpa only [zero_smul, sub_zero, numericalRadius_zero, zero_sub,
        numericalRadius_neg, numericalRadius_smul_one] using h
    exact norm_eq_zero.mp (le_antisymm hc0 (norm_nonneg c))
  · rintro rfl
    intro d
    simpa only [zero_smul, sub_zero, numericalRadius_zero] using
      numericalRadius_nonneg (0 - d • (1 : E →L[ℂ] E))

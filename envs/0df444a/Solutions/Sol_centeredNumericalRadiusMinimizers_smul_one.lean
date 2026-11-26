-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:13:02.036252+00:00
-- url     : https://prove2.me/submissions/ccae9910-67e6-4258-aabc-2308fe51bbc6

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_numericalRadius_one
import Theorems.Thm_numericalRadius_smul_one
import Theorems.Thm_centeredNumericalRadiusMinimizers_add_smul_one
import Theorems.Thm_centeredNumericalRadiusMinimizers_neg
import Theorems.Thm_centeredNumericalRadiusMinimizers_zero
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
attribute [local simp] centeredNumericalRadiusMinimizers_neg
attribute [local simp] centeredNumericalRadiusMinimizers_zero

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
theorem _root_.solution (c : ℂ) :
    centeredNumericalRadiusMinimizers (c • (1 : E →L[ℂ] E)) = {c} := by
  have h := centeredNumericalRadiusMinimizers_add_smul_one
    (0 : E →L[ℂ] E) c
  simpa only [zero_add, centeredNumericalRadiusMinimizers_zero,
    Set.image_singleton, zero_add] using h

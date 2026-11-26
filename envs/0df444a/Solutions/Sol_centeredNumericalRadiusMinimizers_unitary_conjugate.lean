-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_unitary_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:18.041944+00:00
-- url     : https://prove2.me/submissions/348d56ad-118e-4615-b8d2-e87cf3701b42

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
import Theorems.Thm_centeredNumericalRadiusMinimizers_zero
import Theorems.Thm_centeredNumericalRadiusMinimizers_smul_one
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRadius_unitary_conjugate
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
attribute [local simp] centeredNumericalRadiusMinimizers_smul_one

set_option autoImplicit false
open Filter
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Nontrivial E]
omit [Nontrivial E]
theorem _root_.solution [CompleteSpace E]
    (A U : E →L[ℂ] E) (hU : U ∈ unitary (E →L[ℂ] E)) :
    centeredNumericalRadiusMinimizers (U† * A * U) =
      centeredNumericalRadiusMinimizers A := by
  have hcenter (c : ℂ) :
      U† * A * U - c • 1 = U† * (A - c • 1) * U := by
    rw [mul_sub, sub_mul]
    congr 1
    rw [mul_smul_comm, smul_mul_assoc, mul_one]
    change c • 1 = c • (star U * U)
    rw [Unitary.star_mul_self_of_mem hU]
  have hradius (c : ℂ) :
      numericalRadius (U† * A * U - c • 1) =
        numericalRadius (A - c • 1) := by
    rw [hcenter]
    exact numericalRadius_unitary_conjugate (A - c • 1) U hU
  ext c
  constructor
  · intro hc d
    have h := hc d
    rwa [hradius c, hradius d] at h
  · intro hc d
    have h := hc d
    rwa [hradius c, hradius d]

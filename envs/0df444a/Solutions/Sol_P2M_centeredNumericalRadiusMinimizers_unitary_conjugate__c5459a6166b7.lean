-- Prove2me | solution 1 for P2M_centeredNumericalRadiusMinimizers_unitary_conjugate__c5459a6166b7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:42:48.648552+00:00
-- url     : https://prove2.me/submissions/8b11e8c7-400c-4ee0-b581-c786d1271bba

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
import Theorems.Thm_centeredNumericalRadiusMinimizers_unitary_conjugate
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
    centeredNumericalRadiusMinimizers (U * A * U†) =
      centeredNumericalRadiusMinimizers A := by
  simpa only [adjoint_adjoint] using
    centeredNumericalRadiusMinimizers_unitary_conjugate A (U†)
      (Unitary.star_mem hU)

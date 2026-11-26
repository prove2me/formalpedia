-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_eq_setOf_le_of_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:28.295804+00:00
-- url     : https://prove2.me/submissions/b25183b5-bbac-4c6f-a9bd-9cecb8cc5024

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Definitions.Def_Operator_NumericalRange_RadiusAffine
import Theorems.Thm_numericalRadius_one
import Theorems.Thm_numericalRadius_smul_one
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
omit [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E) {c : ℂ}
    (hc : ∀ d : ℂ,
      numericalRadius (A - c • 1) ≤ numericalRadius (A - d • 1)) :
    centeredNumericalRadiusMinimizers A =
      {d : ℂ |
        numericalRadius (A - d • 1) ≤ numericalRadius (A - c • 1)} := by
  ext d
  simp only [centeredNumericalRadiusMinimizers, Set.mem_ofPred_eq]
  constructor
  · exact fun hd => hd c
  · exact fun hd e => hd.trans (hc e)

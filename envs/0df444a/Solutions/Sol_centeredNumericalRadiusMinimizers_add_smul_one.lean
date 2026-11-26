-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_add_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:30.613098+00:00
-- url     : https://prove2.me/submissions/6c754fa5-696d-4543-a3ab-0e27c869ea57

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
    (A : E →L[ℂ] E) (b : ℂ) :
    centeredNumericalRadiusMinimizers (A + b • 1) =
      (fun c : ℂ => c + b) '' centeredNumericalRadiusMinimizers A := by
  ext c
  constructor
  · intro hc
    refine ⟨c - b, ?_, by ring⟩
    intro d
    have h := hc (d + b)
    have hleft : A + b • 1 - c • 1 = A - (c - b) • 1 := by module
    have hright : A + b • 1 - (d + b) • 1 = A - d • 1 := by module
    rw [hleft, hright] at h
    exact h
  · rintro ⟨d, hd, rfl⟩
    intro e
    have h := hd (e - b)
    have hleft : A + b • 1 - (d + b) • 1 = A - d • 1 := by module
    have hright : A + b • 1 - e • 1 = A - (e - b) • 1 := by module
    rw [hleft, hright]
    exact h

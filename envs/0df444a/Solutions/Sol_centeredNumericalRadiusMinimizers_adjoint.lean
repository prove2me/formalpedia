-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:16.530252+00:00
-- url     : https://prove2.me/submissions/6c637791-78c7-4ab0-a072-802b4220644f

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
    (A : E →L[ℂ] E) :
    centeredNumericalRadiusMinimizers (A†) =
      (starRingEnd ℂ) '' centeredNumericalRadiusMinimizers A := by
  have hradius (c : ℂ) :
      numericalRadius (A† - c • 1) =
        numericalRadius (A - star c • 1) := by
    have hop : (A - star c • (1 : E →L[ℂ] E))† = A† - c • 1 := by
      rw [map_sub,
        (adjoint (𝕜 := ℂ) (E := E) (F := E)).map_smulₛₗ,
        adjoint_one, starRingEnd_apply, star_star]
    have h := numericalRadius_adjoint (A - star c • (1 : E →L[ℂ] E))
    rw [hop] at h
    exact h
  ext c
  constructor
  · intro hc
    refine ⟨star c, ?_, by simp⟩
    intro d
    have h := hc (star d)
    rw [hradius c, hradius (star d)] at h
    simpa only [star_star] using h
  · rintro ⟨d, hd, rfl⟩
    intro e
    change numericalRadius (A† - star d • 1) ≤
      numericalRadius (A† - e • 1)
    have h := hd (star e)
    rw [hradius (star d), hradius e]
    simpa only [star_star] using h

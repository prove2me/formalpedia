-- Prove2me | solution 1 for centeredNumericalRadiusMinimizers_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:23.844099+00:00
-- url     : https://prove2.me/submissions/95a3cbc4-3e94-4969-83b8-21d60b28fb84

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
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) :
    centeredNumericalRadiusMinimizers (a • A) =
      (fun c : ℂ => a * c) '' centeredNumericalRadiusMinimizers A := by
  have hscale (z : ℂ) :
      a • A - (a * z) • 1 = a • (A - z • 1) := by module
  ext c
  constructor
  · intro hc
    let d := a⁻¹ * c
    have hac : a * d = c := by
      dsimp only [d]
      field_simp [ha]
    refine ⟨d, ?_, hac⟩
    intro e
    have h := hc (a * e)
    rw [← hac, hscale d, hscale e, numericalRadius_smul,
      numericalRadius_smul] at h
    exact (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr ha)).mp h
  · rintro ⟨d, hd, rfl⟩
    intro e
    let q := a⁻¹ * e
    have haq : a * q = e := by
      dsimp only [q]
      field_simp [ha]
    have h := hd q
    rw [← haq, hscale d, hscale q, numericalRadius_smul,
      numericalRadius_smul]
    exact (mul_le_mul_iff_of_pos_left (norm_pos_iff.mpr ha)).mpr h

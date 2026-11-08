-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsBoundaryNull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:20:45.142108+00:00
-- url     : https://prove2.me/submissions/5593468f-8ff0-458b-b5bf-c984d301cd1f

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Countable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHyperbolicNull
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsComplexVerticalNull

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : (volume : Measure ℍ) (ModularGroup.fd \ ModularGroup.fdo) = 0 := by
  apply lpsHyperbolicNull
  have hcircle : (volume : Measure ℂ) (Metric.sphere 0 1) = 0 := Measure.addHaar_sphere volume 0 1
  have hnull : (volume : Measure ℂ)
      (Metric.sphere 0 1 ∪ {z : ℂ | z.re = (1:ℝ)/2} ∪ {z : ℂ | z.re = -(1:ℝ)/2}) = 0 := by
    apply measure_union_null (measure_union_null hcircle (lpsComplexVerticalNull _))
    exact lpsComplexVerticalNull _
  apply measure_mono_null _ hnull
  rintro z ⟨τ, hτ, rfl⟩
  rcases hτ with ⟨⟨hn,hr⟩,ho⟩
  by_cases h : 1 < Complex.normSq (τ : ℂ)
  · have hre : |τ.re| = (1:ℝ)/2 := le_antisymm hr (not_lt.mp fun hh => ho ⟨h,hh⟩)
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)).mp hre with hp | hm
    · exact Or.inl (Or.inr hp)
    · apply Or.inr
      change τ.re = -(1:ℝ)/2
      linarith [hm]
  · have hn' : Complex.normSq (τ : ℂ) = 1 := le_antisymm (not_lt.mp h) hn
    apply Or.inl ∘ Or.inl
    rw [Metric.mem_sphere, dist_zero_right]
    have hp : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
    rw [Complex.normSq_eq_norm_sq] at hn'
    nlinarith
end QEC.Coding.TannerLiftedProduct

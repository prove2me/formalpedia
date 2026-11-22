-- Prove2me | solution 1 for ProbabilityTheory.map_cdfUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:03.593987+00:00
-- url     : https://prove2.me/submissions/59e6e074-9727-4cf4-b230-a089cd3edd15

module
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Definitions.Def_LeanPool_Copula_Distribution_ProbabilityIntegralTransform
public import Theorems.Thm_ProbabilityTheory_coe_cdfUnit
public import Theorems.Thm_ProbabilityTheory_measurable_cdfUnit
public import Theorems.Thm_ProbabilityTheory_exists_cdf_eq_of_continuous
attribute [local simp] ProbabilityTheory.coe_cdfUnit
attribute [local fun_prop] ProbabilityTheory.measurable_cdfUnit

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped unitInterval Topology
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : Continuous (cdf μ)) : μ.map (cdfUnit μ) = volume := by
  apply Measure.ext_of_Iic
  intro u
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (μ.map (cdfUnit μ)).real (Iic u) = volume.real (Iic u)
  rw [map_measureReal_apply (measurable_cdfUnit μ) measurableSet_Iic]
  have hvol : volume.real (Iic u) = (u : ℝ) := by
    simp [Measure.real, u.property.1]
  rw [hvol]
  change μ.real {x | cdf μ x ≤ (u : ℝ)} = (u : ℝ)
  apply le_antisymm
  · by_contra! h
    obtain ⟨r, hur, hr⟩ := exists_between h
    have hr0 : 0 < r := lt_of_le_of_lt u.property.1 hur
    have hr1 : r < 1 := hr.trans_le measureReal_le_one
    obtain ⟨y, hy⟩ := exists_cdf_eq_of_continuous μ hc hr0 hr1
    have hsub : {x | cdf μ x ≤ (u : ℝ)} ⊆ Iic y := by
      intro x hx
      change x ≤ y
      by_contra! hxy
      have hm := monotone_cdf μ hxy.le
      change cdf μ x ≤ (u : ℝ) at hx
      linarith
    have hm := measureReal_mono (μ := μ) hsub
    rw [← cdf_eq_real, hy] at hm
    linarith
  · by_cases hu0 : (u : ℝ) = 0
    · rw [hu0]
      exact measureReal_nonneg
    by_cases hu1 : (u : ℝ) = 1
    · have he : {x | cdf μ x ≤ (u : ℝ)} = univ := by
        ext x
        simp [hu1, cdf_le_one]
      rw [he, probReal_univ, hu1]
    · obtain ⟨y, hy⟩ := exists_cdf_eq_of_continuous μ hc
        (lt_of_le_of_ne u.property.1 (Ne.symm hu0))
        (lt_of_le_of_ne u.property.2 hu1)
      have hsub : Iic y ⊆ {x | cdf μ x ≤ (u : ℝ)} := by
        intro x hx
        exact (monotone_cdf μ hx).trans hy.le
      have hm := measureReal_mono (μ := μ) hsub
      rwa [← cdf_eq_real, hy] at hm
end ProbabilityTheory

-- Prove2me | solution 1 for OpenCategoryPAC.upper_bound_alien_cdf
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:39:57.023054+00:00
-- url     : https://prove2.me/submissions/06e60d33-6c0d-42bc-8ad0-2df65e5d5f61

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
namespace OpenCategoryPAC

lemma ub_prob (μ0 μa : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    IsProbabilityMeasure (mixture α μ0 μa) := by
  constructor
  simp only [mixture, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hα0]; simp

lemma ub_mix (μ0 μa : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) [IsProbabilityMeasure (mixture α μ0 μa)] (t : ℝ) :
    cdf (mixture α μ0 μa) t = (1 - α) * cdf μ0 t + α * cdf μa t := by
  rw [cdf_eq_real, cdf_eq_real, cdf_eq_real]
  simp only [mixture, measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top]) (by simp [ENNReal.mul_eq_top]),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal hα0]

theorem upper_bound_alien_cdf (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α α' : ℝ) (hα0 : 0 < α)
    (hαα' : α ≤ α') (hα'1 : α' ≤ 1) (hm : μm = mixture α μ0 μa) :
    (Monotone (alienCDF α' (cdf μm) (cdf μ0)) ∧
      Tendsto (alienCDF α' (cdf μm) (cdf μ0)) atBot (𝓝 0) ∧
      Tendsto (alienCDF α' (cdf μm) (cdf μ0)) atTop (𝓝 1) ∧
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ⇑(cdf ν) = alienCDF α' (cdf μm) (cdf μ0)) ∧
    (∀ t : ℝ, alienCDF α' (cdf μm) (cdf μ0) t - cdf μa t =
      (α - α') * (cdf μm t - cdf μ0 t) / (α * α')) ∧
    (IsAdmissible μ0 μm → ∀ t : ℝ, cdf μa t ≤ alienCDF α' (cdf μm) (cdf μ0) t) := by
  have hα'0 : 0 < α' := lt_of_lt_of_le hα0 hαα'
  have hmix : ∀ t, cdf μm t = (1 - α) * cdf μ0 t + α * cdf μa t := by
    intro t; subst hm; exact ub_mix μ0 μa α hα0.le (by linarith) t
  set β := α / α' with hβ
  have hβ0 : 0 ≤ β := div_nonneg hα0.le hα'0.le
  have hβ1 : β ≤ 1 := (div_le_one hα'0).2 hαα'
  haveI hν := ub_prob μ0 μa β hβ0 hβ1
  have hcdf : ⇑(cdf (mixture β μ0 μa)) = alienCDF α' (cdf μm) (cdf μ0) := by
    funext t
    rw [ub_mix μ0 μa β hβ0 hβ1 t]
    simp only [alienCDF, hmix, hβ]
    field_simp; ring
  have hdiff : ∀ t : ℝ, alienCDF α' (cdf μm) (cdf μ0) t - cdf μa t =
      (α - α') * (cdf μm t - cdf μ0 t) / (α * α') := by
    intro t; simp only [alienCDF, hmix]; field_simp; ring
  refine ⟨⟨?_, ?_, ?_, ⟨_, hν, hcdf⟩⟩, hdiff, ?_⟩
  · rw [← hcdf]; exact (cdf (mixture β μ0 μa)).mono
  · rw [← hcdf]; exact tendsto_cdf_atBot _
  · rw [← hcdf]; exact tendsto_cdf_atTop _
  · intro hadm t
    have h1 := hdiff t
    have h2 : cdf μm t - cdf μ0 t ≤ 0 := by have := hadm t; linarith
    have h3 : 0 ≤ (α - α') * (cdf μm t - cdf μ0 t) / (α * α') :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) h2) (by positivity)
    linarith

end OpenCategoryPAC
open OpenCategoryPAC in
theorem solution (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α α' : ℝ) (hα0 : 0 < α)
    (hαα' : α ≤ α') (hα'1 : α' ≤ 1) (hm : μm = mixture α μ0 μa) :
    (Monotone (alienCDF α' (cdf μm) (cdf μ0)) ∧
      Tendsto (alienCDF α' (cdf μm) (cdf μ0)) atBot (𝓝 0) ∧
      Tendsto (alienCDF α' (cdf μm) (cdf μ0)) atTop (𝓝 1) ∧
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ⇑(cdf ν) = alienCDF α' (cdf μm) (cdf μ0)) ∧
    (∀ t : ℝ, alienCDF α' (cdf μm) (cdf μ0) t - cdf μa t =
      (α - α') * (cdf μm t - cdf μ0 t) / (α * α')) ∧
    (IsAdmissible μ0 μm → ∀ t : ℝ, cdf μa t ≤ alienCDF α' (cdf μm) (cdf μ0) t) :=
  upper_bound_alien_cdf μ0 μa μm α α' hα0 hαα' hα'1 hm

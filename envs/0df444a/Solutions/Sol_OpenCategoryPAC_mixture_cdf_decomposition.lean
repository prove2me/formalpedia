-- Prove2me | solution 1 for OpenCategoryPAC.mixture_cdf_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:38:38.999264+00:00
-- url     : https://prove2.me/submissions/f2e4f0cd-f421-44ad-a467-b5a0dddcc3bd

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
namespace OpenCategoryPAC

theorem mixture_cdf_decomposition (μ0 μa : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    IsProbabilityMeasure (mixture α μ0 μa) ∧
    (∀ t : ℝ, cdf (mixture α μ0 μa) t = (1 - α) * cdf μ0 t + α * cdf μa t) ∧
    (∀ t : ℝ, cdf μa t = alienCDF α (cdf (mixture α μ0 μa)) (cdf μ0) t) := by
  have hP : IsProbabilityMeasure (mixture α μ0 μa) := by
    constructor
    simp only [mixture, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (by linarith) hα0.le]; simp
  have h2 : ∀ t : ℝ, cdf (mixture α μ0 μa) t = (1 - α) * cdf μ0 t + α * cdf μa t := by
    intro t
    rw [cdf_eq_real, cdf_eq_real, cdf_eq_real]
    simp only [mixture, measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top]) (by simp [ENNReal.mul_eq_top]),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal hα0.le]
  refine ⟨hP, h2, fun t => ?_⟩
  simp only [alienCDF, h2]
  field_simp; ring

end OpenCategoryPAC
open OpenCategoryPAC in
theorem solution (μ0 μa : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    IsProbabilityMeasure (mixture α μ0 μa) ∧
    (∀ t : ℝ, cdf (mixture α μ0 μa) t = (1 - α) * cdf μ0 t + α * cdf μa t) ∧
    (∀ t : ℝ, cdf μa t = alienCDF α (cdf (mixture α μ0 μa)) (cdf μ0) t) :=
  mixture_cdf_decomposition μ0 μa α hα0 hα1

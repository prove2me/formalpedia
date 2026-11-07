-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_section_area
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:52.262461+00:00
-- url     : https://prove2.me/submissions/b601b372-83ff-4353-933b-841b8e418e99

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeVolume
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialCone_section
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialCone_section_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_ball_le_coneSlopeSq_mul
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_coneSlopeSq_mul_le_ball
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_coneSlopeSq_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_volume_disk_sqrt
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (z : ℝ) :
    volume {y : Transverse | axialEquiv.symm (z,y) ∈ axialCone c} =
      (Icc 0 c).indicator (fun z => ENNReal.ofReal (Real.pi * (coneSlopeSq c * z^2))) z +
      (Ioc c 1).indicator (fun z => ENNReal.ofReal (Real.pi * (1-z^2))) z := by
  by_cases hz : z ∈ Icc 0 c
  · have hnot : z ∉ Ioc c 1 := by intro h; exact (not_lt_of_ge hz.2) h.1
    rw [indicator_of_mem hz, indicator_of_notMem hnot, add_zero,
      axialCone_section hc0 hc1.le hz.1 (hz.2.trans hc1.le),
      min_eq_left (coneSlopeSq_mul_le_ball hc0 hc1.le hz.1 hz.2), volume_disk_sqrt]
    exact mul_nonneg (coneSlopeSq_nonneg hc0 hc1.le) (sq_nonneg z)
  · by_cases hz2 : z ∈ Ioc c 1
    · rw [indicator_of_notMem hz, indicator_of_mem hz2, zero_add,
        axialCone_section hc0 hc1.le (hc0.le.trans hz2.1.le) hz2.2,
        min_eq_right (ball_le_coneSlopeSq_mul hc0 hz2.1.le), volume_disk_sqrt]
      nlinarith [hc0.le.trans hz2.1.le, hz2.2]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz2, zero_add,
        axialCone_section_empty hc0, measure_empty]
      simp only [mem_Icc, mem_Ioc, not_and_or, not_le, not_lt] at hz hz2
      rcases hz with hz | hz
      · exact Or.inl hz
      · rcases hz2 with hz2 | hz2
        · exact False.elim ((not_le_of_gt hz) hz2)
        · exact Or.inr hz2
end QEC.Coding.ProbabilisticConstruction.SphericalCap

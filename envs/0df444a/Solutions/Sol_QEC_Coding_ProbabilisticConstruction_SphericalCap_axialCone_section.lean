-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.axialCone_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:47.212174+00:00
-- url     : https://prove2.me/submissions/cf13de70-2163-4ac1-ace2-98bb15f92131

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_coneSlopeSq_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_cone_slice_iff
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_norm_sq_axial
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {c z : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    {y : Transverse | axialEquiv.symm (z, y) ∈ axialCone c} =
      closedBall 0 (Real.sqrt (min (coneSlopeSq c * z ^ 2) (1 - z ^ 2))) := by
  ext y
  have hnorm := norm_sq_axial (axialEquiv.symm (z, y))
  simp only [MeasurableEquiv.apply_symm_apply] at hnorm
  have hfst : (axialEquiv.symm (z, y)) 0 = z := by
    change (axialEquiv (axialEquiv.symm (z, y))).1 = z
    rw [MeasurableEquiv.apply_symm_apply]
  have hroot : ‖axialEquiv.symm (z, y)‖ = Real.sqrt (z ^ 2 + ‖y‖ ^ 2) := by
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hmin : 0 ≤ min (coneSlopeSq c * z ^ 2) (1 - z ^ 2) := by
    apply le_min
    · exact mul_nonneg (coneSlopeSq_nonneg hc0 hc1) (sq_nonneg _)
    · nlinarith
  simp only [mem_setOf_eq, axialCone, hfst, hroot, mem_closedBall, dist_zero_right,
    Real.le_sqrt (norm_nonneg _) hmin, le_min_iff]
  rw [cone_slice_iff hc0 (norm_nonneg y)]
  have hsq : 0 ≤ z ^ 2 + ‖y‖ ^ 2 := by positivity
  have he := Real.sq_sqrt hsq
  have hr := Real.sqrt_nonneg (z ^ 2 + ‖y‖ ^ 2)
  constructor
  · rintro ⟨hb, _, hc⟩
    exact ⟨hc, by nlinarith⟩
  · rintro ⟨hc, hb⟩
    exact ⟨by nlinarith, hz0, hc⟩
end QEC.Coding.ProbabilisticConstruction.SphericalCap

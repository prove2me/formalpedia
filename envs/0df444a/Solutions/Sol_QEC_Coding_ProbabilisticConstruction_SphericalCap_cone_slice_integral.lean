-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_slice_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:26.890278+00:00
-- url     : https://prove2.me/submissions/be16fb0a-fb4a-4ab5-850d-8cd1d8b06648

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    (∫ z in (0 : ℝ)..c, Real.pi * (coneSlopeSq c * z ^ 2)) +
      (∫ z in c..1, Real.pi * (1 - z ^ 2)) =
        (2 * Real.pi / 3) * (1 - c) := by
  have h0 : c ≠ 0 := ne_of_gt hc0
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegral.intervalIntegrable_pow 2)]
  simp only [intervalIntegral.integral_const, integral_pow, sub_zero,
    zero_pow (by decide : 3 ≠ 0), one_pow, smul_eq_mul]
  unfold coneSlopeSq
  field_simp
  <;> ring
end QEC.Coding.ProbabilisticConstruction.SphericalCap

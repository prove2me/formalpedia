-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.cone_slice_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:36:55.45249+00:00
-- url     : https://prove2.me/submissions/9de306c5-b674-4c77-af9a-11e731501462

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
theorem _root_.solution {c z q : ℝ} (hc : 0 < c) (hq : 0 ≤ q) :
    c * Real.sqrt (z ^ 2 + q ^ 2) ≤ z ↔
      0 ≤ z ∧ q ^ 2 ≤ coneSlopeSq c * z ^ 2 := by
  have hs : 0 ≤ z ^ 2 + q ^ 2 := by positivity
  have hr : 0 ≤ Real.sqrt (z ^ 2 + q ^ 2) := Real.sqrt_nonneg _
  have he := Real.sq_sqrt hs
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  constructor
  · intro h
    have hz : 0 ≤ z := le_trans (mul_nonneg hc.le hr) h
    refine ⟨hz, ?_⟩
    have hsq : c ^ 2 * (z ^ 2 + q ^ 2) ≤ z ^ 2 := by
      have hsq := (sq_le_sq₀ (mul_nonneg hc.le hr) hz).mpr h
      simpa only [mul_pow, he] using hsq
    rw [coneSlopeSq, div_mul_eq_mul_div, le_div_iff₀ hc2]
    nlinarith
  · rintro ⟨hz, hq2⟩
    rw [coneSlopeSq, div_mul_eq_mul_div, le_div_iff₀ hc2] at hq2
    apply (sq_le_sq₀ (mul_nonneg hc.le hr) hz).mp
    rw [mul_pow, he]
    nlinarith
end QEC.Coding.ProbabilisticConstruction.SphericalCap

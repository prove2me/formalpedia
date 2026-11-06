-- Prove2me | solution 1 for ProbabilityTheory.measure_levyBadGrid_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:30:44.259813+00:00
-- url     : https://prove2.me/submissions/33499cd5-d84b-4da9-a383-073cb976960d

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Probability.Martingale.OptionalStopping
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_measure_countable_sup_levyBandPath_ge
import Theorems.Thm_ProbabilityTheory_integral_sq_levySlice_le
import Theorems.Thm_ProbabilityTheory_levySlice_subset
import Theorems.Thm_ProbabilityTheory_levySlice_finite_mass
import Theorems.Thm_ProbabilityTheory_measurableSet_levySlice
import Theorems.Thm_ProbabilityTheory_levyGrid_countable
import Theorems.Thm_ProbabilityTheory_levyGrid_subset_Icc
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (T j : ℕ) :
    μ (levyBadGrid hd hν T j) ≤ ENNReal.ofReal (Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j) := by
  set ε : ℝ≥0 := ((2 : ℝ≥0)⁻¹) ^ j with hεdef
  have hεR : (ε : ℝ) = ((2 : ℝ)⁻¹) ^ j := by rw [hεdef]; push_cast; ring
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hev : levyBadGrid hd hν T j
      = {ω | ∃ t ∈ levyGrid T, (ε : ℝ) ≤ |levyBandPath K X ν (levySlice hν j) t ω|} := by
    simp only [levyBadGrid, hεR]
  rw [hev]
  refine (measure_countable_sup_levyBandPath_ge hd hν (measurableSet_levySlice hν j)
    (levySlice_subset hν j) (levySlice_finite_mass hν j) (Nat.cast_nonneg T)
    (levyGrid_countable T) (levyGrid_subset_Icc T) hεpos).trans ?_
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hIle : (∫ x in levySlice hν j, x ^ 2 ∂ν) ≤ ((16 : ℝ)⁻¹) ^ j := integral_sq_levySlice_le hν j
  have hsqrt16 : Real.sqrt (((16 : ℝ)⁻¹) ^ j) = ((4 : ℝ)⁻¹) ^ j := by
    have hthis : (((4 : ℝ)⁻¹) ^ j) ^ 2 = ((16 : ℝ)⁻¹) ^ j := by
      rw [← pow_mul, mul_comm, pow_mul, show ((4 : ℝ)⁻¹) ^ 2 = (16 : ℝ)⁻¹ by norm_num]
    rw [← hthis, Real.sqrt_sq (by positivity)]
  have step1 : Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν)
      ≤ Real.sqrt (T : ℝ) * ((4 : ℝ)⁻¹) ^ j := by
    rw [← hsqrt16, ← Real.sqrt_mul hTnn]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hIle hTnn)
  have step2 : Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j * ((2 : ℝ)⁻¹) ^ j
      = Real.sqrt (T : ℝ) * ((4 : ℝ)⁻¹) ^ j := by
    rw [mul_assoc, ← mul_pow, show (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ by norm_num]
  have hreal : Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν) / (ε : ℝ)
      ≤ Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j := by
    rw [hεR, div_le_iff₀ (by positivity), step2]
    exact step1
  calc ENNReal.ofReal (Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν)) / (ε : ℝ≥0∞)
      = ENNReal.ofReal (Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν))
          / ENNReal.ofReal (ε : ℝ) := by rw [ENNReal.ofReal_coe_nnreal]
    _ = ENNReal.ofReal (Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν) / (ε : ℝ)) :=
        (ENNReal.ofReal_div_of_pos (by rw [hεR]; positivity)).symm
    _ ≤ ENNReal.ofReal (Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j) := ENNReal.ofReal_le_ofReal hreal

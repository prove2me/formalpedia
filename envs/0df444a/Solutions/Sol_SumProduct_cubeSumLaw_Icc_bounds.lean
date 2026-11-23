-- Prove2me | solution 1 for SumProduct.cubeSumLaw_Icc_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:22:03.011436+00:00
-- url     : https://prove2.me/submissions/cf0cdbb6-643d-41eb-99d3-705b802f8969

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLaw_Icc_eq_sinc_integral
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
import Theorems.Thm_SumProduct_sinc_power_integral_bounds
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    1 / Real.sqrt (n + 1 : ℝ) ≤ (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal ∧
      (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal ≤
        5 / Real.sqrt (n + 1 : ℝ) := by
  have hN : 2 ≤ n + 1 := Nat.succ_le_succ hn
  have hEq := cubeSumLaw_Icc_eq_sinc_integral n hn
  have hBounds := sinc_power_integral_bounds (n + 1) hN
  have hLower :
      Real.pi / Real.sqrt (n + 1 : ℝ) ≤ ∫ t : ℝ, (Real.sinc t) ^ (n + 1) := by
    simpa [Nat.cast_add, Nat.cast_one] using hBounds.1
  have hUpper :
      ∫ t : ℝ, (Real.sinc t) ^ (n + 1) ≤
        5 * Real.pi / Real.sqrt (n + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using hBounds.2
  have hπnonneg : 0 ≤ (Real.pi)⁻¹ := inv_nonneg.mpr Real.pi_pos.le
  rw [hEq]
  constructor
  · calc
      1 / Real.sqrt (n + 1 : ℝ)
          = (Real.pi)⁻¹ * (Real.pi / Real.sqrt (n + 1 : ℝ)) := by
        field_simp [Real.pi_ne_zero]
      _ ≤ (Real.pi)⁻¹ * ∫ t : ℝ, (Real.sinc t) ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_left hLower hπnonneg
  · calc
      (Real.pi)⁻¹ * ∫ t : ℝ, (Real.sinc t) ^ (n + 1)
          ≤ (Real.pi)⁻¹ * (5 * Real.pi / Real.sqrt (n + 1 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hUpper hπnonneg
      _ = 5 / Real.sqrt (n + 1 : ℝ) := by
        field_simp [Real.pi_ne_zero]
end SumProduct

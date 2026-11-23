-- Prove2me | solution 1 for SumProduct.cubeSection_fin_one_volume_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:24:54.839873+00:00
-- url     : https://prove2.me/submissions/d57c9ade-6a9a-472c-8b6c-b186dbebe6b2

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLaw_Icc_toReal_eq
import Theorems.Thm_SumProduct_cubeSumLaw_Icc_bounds
import Theorems.Thm_SumProduct_mem_boxMult
import Theorems.Thm_SumProduct_mem_cubeSection
attribute [local simp] SumProduct.mem_boxMult
attribute [local simp] SumProduct.mem_cubeSection



set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ) ≤
        (volume (cubeSection (Fin n) 1)).toReal ∧
      (volume (cubeSection (Fin n) 1)).toReal ≤
        5 * (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ) := by
  have hP := cubeSumLaw_Icc_bounds n hn
  have hEq := cubeSumLaw_Icc_toReal_eq n
  have hpow : 0 < (2 : ℝ) ^ n := pow_pos zero_lt_two n
  constructor
  · calc
      (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ)
          = (2 : ℝ) ^ n * (1 / Real.sqrt (n + 1 : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ n *
          ((volume (cubeSection (Fin n) 1)).toReal / (2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_left (by simpa [hEq] using hP.1) hpow.le
      _ = (volume (cubeSection (Fin n) 1)).toReal := by
        field_simp [hpow.ne']
  · calc
      (volume (cubeSection (Fin n) 1)).toReal
          = (2 : ℝ) ^ n *
          ((volume (cubeSection (Fin n) 1)).toReal / (2 : ℝ) ^ n) := by
        field_simp [hpow.ne']
      _ ≤ (2 : ℝ) ^ n * (5 / Real.sqrt (n + 1 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [hEq] using hP.2) hpow.le
      _ = 5 * (2 : ℝ) ^ n / Real.sqrt (n + 1 : ℝ) := by ring
end SumProduct

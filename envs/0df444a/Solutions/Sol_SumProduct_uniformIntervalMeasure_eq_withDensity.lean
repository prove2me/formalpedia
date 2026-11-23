-- Prove2me | solution 1 for SumProduct.uniformIntervalMeasure_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:54.946932+00:00
-- url     : https://prove2.me/submissions/e24e9cb7-8f37-4018-9b74-e11e99ee467e

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
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
theorem _root_.solution :
    uniformIntervalMeasure =
      volume.withDensity
        (fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) x) := by
  rw [uniformIntervalMeasure]
  calc
    ((2 : NNReal)⁻¹) • volume.restrict (Set.Icc (-1 : ℝ) 1)
        = (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1) := by
          ext s hs
          rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, ENNReal.coe_inv_two, smul_eq_mul]
    _ = (volume.restrict (Set.Icc (-1 : ℝ) 1)).withDensity
          ((2 : ℝ≥0∞)⁻¹ • (1 : ℝ → ℝ≥0∞)) := by
          symm
          rw [withDensity_smul]
          rw [withDensity_one]
          fun_prop
    _ = volume.withDensity
          (fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (2 : ℝ≥0∞)⁻¹) x) := by
          rw [withDensity_indicator measurableSet_Icc]
          congr 1
          ext x
          simp [Pi.smul_apply]
end SumProduct

-- Prove2me | solution 1 for SumProduct.charFun_uniformIntervalMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:52:02.830313+00:00
-- url     : https://prove2.me/submissions/a5f2d91a-718a-4328-8379-77c749a49222

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
theorem _root_.solution (t : ℝ) :
    charFun uniformIntervalMeasure t = (Real.sinc t : ℂ) := by
  rw [uniformIntervalMeasure, charFun_apply_real]
  simp
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  by_cases ht : t = 0
  · subst t
    simp [Real.sinc_zero]
    norm_num [NNReal.smul_def]
  · have hsubst :
        (∫ x in (-1 : ℝ)..1, Complex.exp (↑t * ↑x * Complex.I)) =
          t⁻¹ • ∫ y in (-t)..t, Complex.exp (↑y * Complex.I) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (intervalIntegral.integral_comp_mul_left
          (f := fun y : ℝ => Complex.exp (↑y * Complex.I))
          (a := (-1 : ℝ)) (b := 1) (c := t) ht)
    rw [hsubst, integral_exp_mul_I_eq_sinc]
    norm_num [NNReal.smul_def]
    field_simp [ht]
end SumProduct

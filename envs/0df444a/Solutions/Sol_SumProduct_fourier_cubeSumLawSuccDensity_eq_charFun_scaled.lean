-- Prove2me | solution 1 for SumProduct.fourier_cubeSumLawSuccDensity_eq_charFun_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:06:03.146786+00:00
-- url     : https://prove2.me/submissions/c613106a-24fa-47cc-9ccb-8a285782411e

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLaw_succ_eq_withDensity
import Theorems.Thm_SumProduct_measurable_cubeSumLawSuccDensity
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_ae_lt_top
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
theorem _root_.solution (n : ℕ) (w : ℝ) :
    𝓕 (fun x : ℝ => ((cubeSumLawSuccDensity n x).toReal : ℂ)) w =
      charFun (cubeSumLaw (n + 1)) ((-2 * Real.pi) * w) := by
  rw [Real.fourier_eq]
  rw [charFun_apply_real]
  rw [cubeSumLaw_succ_eq_withDensity n]
  rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_cubeSumLawSuccDensity n)
      (cubeSumLawSuccDensity_ae_lt_top n)]
  simp [Real.fourierChar_apply, Circle.smul_def, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc]
end SumProduct

-- Prove2me | solution 1 for SumProduct.cubeSumLawSuccDensity_toReal_eq_half_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:08:15.042804+00:00
-- url     : https://prove2.me/submissions/ae927ed5-a2b9-4f4e-95e6-bd2270074bba

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLaw_measure_Icc_toReal_eq_integral_density
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_toReal_eq_half_measure_Icc

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution
    (n : ℕ) (hn : 1 ≤ n) (z : ℝ) :
    (cubeSumLawSuccDensity n z).toReal =
      (1 / 2 : ℝ) * ∫ x in (z - 1)..(z + 1),
        (cubeSumLawSuccDensity (n - 1) x).toReal := by
  rw [cubeSumLawSuccDensity_toReal_eq_half_measure_Icc]
  congr 1
  have hn' : (n - 1) + 1 = n := by omega
  calc
    (cubeSumLaw n (Set.Icc (z - 1) (z + 1))).toReal =
        (cubeSumLaw ((n - 1) + 1) (Set.Icc (z - 1) (z + 1))).toReal := by rw [hn']
    _ = ∫ x in Set.Icc (z - 1) (z + 1),
        (cubeSumLawSuccDensity (n - 1) x).toReal := by
      rw [cubeSumLaw_measure_Icc_toReal_eq_integral_density]
    _ = ∫ x in (z - 1)..(z + 1),
        (cubeSumLawSuccDensity (n - 1) x).toReal := by
      have hle : z - 1 ≤ z + 1 := by linarith
      rw [intervalIntegral.integral_of_le hle]
      rw [← integral_Icc_eq_integral_Ioc]
end SumProduct

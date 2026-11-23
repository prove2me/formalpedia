-- Prove2me | solution 1 for SumProduct.cubeSumLawSuccDensity_toReal_eq_half_measure_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:58:38.072831+00:00
-- url     : https://prove2.me/submissions/3abc82d2-ef32-424a-bbb8-58590cfd95a5

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_eq_half_measure_Icc

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) (z : ℝ) :
    (cubeSumLawSuccDensity n z).toReal =
      (1 / 2 : ℝ) * (cubeSumLaw n (Set.Icc (z - 1) (z + 1))).toReal := by
  rw [cubeSumLawSuccDensity_eq_half_measure_Icc]
  rw [ENNReal.toReal_mul]
  norm_num
end SumProduct

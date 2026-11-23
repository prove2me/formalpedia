-- Prove2me | solution 1 for SumProduct.cubeSumLaw_succ_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:59:27.168839+00:00
-- url     : https://prove2.me/submissions/390ca7e1-a2a5-4ae3-8907-3704814265a1

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLaw_succ_eq_conv
import Theorems.Thm_SumProduct_uniformIntervalMeasure_eq_withDensity
import Theorems.Thm_SumProduct_conv_withDensity_right_eq

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) :
    cubeSumLaw (n + 1) = volume.withDensity (cubeSumLawSuccDensity n) := by
  rw [cubeSumLaw_succ_eq_conv, uniformIntervalMeasure_eq_withDensity]
  exact conv_withDensity_right_eq (cubeSumLaw n) (measurable_const.indicator measurableSet_Icc)
end SumProduct

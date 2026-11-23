-- Prove2me | solution 1 for SumProduct.cubeSumLaw_succ_eq_conv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:56:43.130256+00:00
-- url     : https://prove2.me/submissions/97df42a6-cb59-42ff-b1c2-235d60002b71

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_charFun_uniformIntervalMeasure
import Theorems.Thm_SumProduct_charFun_cubeSumLaw_eq_sinc_pow

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) :
    cubeSumLaw (n + 1) = cubeSumLaw n ∗ uniformIntervalMeasure := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_cubeSumLaw_eq_sinc_pow, charFun_conv, charFun_cubeSumLaw_eq_sinc_pow,
    charFun_uniformIntervalMeasure, pow_succ]
end SumProduct

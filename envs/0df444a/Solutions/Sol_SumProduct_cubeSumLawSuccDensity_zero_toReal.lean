-- Prove2me | solution 1 for SumProduct.cubeSumLawSuccDensity_zero_toReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:58:48.760814+00:00
-- url     : https://prove2.me/submissions/550507d4-9878-4fe9-8c70-c12ab6c18309

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore
import Theorems.Thm_SumProduct_cubeSumLawSuccDensity_zero

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) :
    (cubeSumLawSuccDensity n 0).toReal =
      (1 / 2 : ℝ) * (cubeSumLaw n (Set.Icc (-1 : ℝ) 1)).toReal := by
  rw [cubeSumLawSuccDensity_zero]
  rw [ENNReal.toReal_mul]
  norm_num
end SumProduct

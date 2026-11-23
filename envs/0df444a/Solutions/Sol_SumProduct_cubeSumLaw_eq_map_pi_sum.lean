-- Prove2me | solution 1 for SumProduct.cubeSumLaw_eq_map_pi_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:53:32.850032+00:00
-- url     : https://prove2.me/submissions/6036c047-f7e6-4d85-b435-829bbadbd307

import Definitions.Def_SumProduct_CubeSection
import Definitions.Def_SumProduct_SincIntegral
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_SumProduct_CubeSectionCore

set_option autoImplicit true
open MeasureTheory
open scoped ENNReal MeasureTheory FourierTransform
open SumProduct
noncomputable section
namespace SumProduct
theorem _root_.solution (n : ℕ) :
    cubeSumLaw n =
      (Measure.pi fun _ : Fin n => uniformIntervalMeasure).map (fun x => ∑ i, x i) := by
  rw [cubeSumLaw, uniformCubeMeasure_eq_pi_uniformIntervalMeasure]
  rfl
end SumProduct

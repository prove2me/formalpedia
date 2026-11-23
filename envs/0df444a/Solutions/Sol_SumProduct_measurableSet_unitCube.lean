-- Prove2me | solution 1 for SumProduct.measurableSet_unitCube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:08:13.20768+00:00
-- url     : https://prove2.me/submissions/abb14bd8-26f2-4570-a4c7-c752bae89cf8

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
theorem _root_.solution (n : ℕ) : MeasurableSet (unitCube n) := by
  exact isClosed_Icc.measurableSet
end SumProduct

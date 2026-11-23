-- Prove2me | solution 1 for SumProduct.measurableSet_unitBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:50:08.584821+00:00
-- url     : https://prove2.me/submissions/90b4bcea-09aa-45e5-8084-a7d404c96e36

import Mathlib
import Definitions.Def_SumProduct_Boxes

set_option autoImplicit true
open scoped NumberField
open Pointwise
open SumProduct
open scoped Classical
open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace SumProduct
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (r : ℝ) :
    MeasurableSet (unitBox K r) := by
  rw [unitBox, Set.setOf_and]
  refine (IsClosed.inter ?_ ?_).measurableSet
  · rw [Set.setOf_forall]
    exact isClosed_iInter fun w =>
      isClosed_le (continuous_abs.comp (continuous_apply w)) continuous_const
  · exact isClosed_le
      (continuous_abs.comp (continuous_finsetSum _ fun w _ => continuous_apply w)) continuous_const
end SumProduct

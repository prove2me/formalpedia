-- Prove2me | solution 1 for Set.Countable.isUniversallyNull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:22:33.197227+00:00
-- url     : https://prove2.me/submissions/a3a45115-6dab-40b0-add7-44628ed0b3dc

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_AddUN_UniversallyNull

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}
namespace MeasureTheory
namespace _root_.Set.Countable
theorem _root_.solution (hA : A.Countable) : IsUniversallyNull A :=
  fun μ _ _ ↦ hA.measure_zero μ
end _root_.Set.Countable
end MeasureTheory

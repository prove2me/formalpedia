-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.measure_centeredFrequencyBad_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:37:42.399166+00:00
-- url     : https://prove2.me/submissions/df3e60b8-c4db-47b1-a044-e48aa771b8f1

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_measure_centeredCharacterSum_ge_le
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_measure_centeredCharacterSum_le_neg_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSpaceChoiceValue
attribute [local instance] QEC.Coding.FiberBundle.TwistGraph.instMeasurableSingletonClassChoiceValue
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    (r typeCount ell : Nat)
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (frequency : ZMod ell)
    (hfrequency : frequency ≠ 0) :
    (RandomTwist.distribution r typeCount ell).toMeasure.real
        {sample | CenteredFrequencyBad frequency sample} ≤
      2 * Real.exp (-(typeCount : Real) / 20000000000) := by
  let μ :=
    (RandomTwist.distribution r typeCount ell).toMeasure
  let upper : Set (RandomTwist.Sample r typeCount ell) :=
    {sample |
      (typeCount : Real) / 50000 ≤
        centeredCharacterSum frequency sample}
  let lower : Set (RandomTwist.Sample r typeCount ell) :=
    {sample |
      centeredCharacterSum frequency sample ≤
        -((typeCount : Real) / 50000)}
  have hSubset :
      {sample | CenteredFrequencyBad frequency sample} ⊆
        upper ∪ lower := by
    intro sample hBad
    change (typeCount : Real) / 50000 <
      |centeredCharacterSum frequency sample| at hBad
    by_cases hNonneg :
        0 ≤ centeredCharacterSum frequency sample
    · left
      change (typeCount : Real) / 50000 ≤
        centeredCharacterSum frequency sample
      rw [abs_of_nonneg hNonneg] at hBad
      exact hBad.le
    · right
      change centeredCharacterSum frequency sample ≤
        -((typeCount : Real) / 50000)
      rw [abs_of_neg (lt_of_not_ge hNonneg)] at hBad
      linarith
  calc
    μ.real {sample | CenteredFrequencyBad frequency sample} ≤
        μ.real (upper ∪ lower) :=
      MeasureTheory.measureReal_mono hSubset
    _ ≤ μ.real upper + μ.real lower :=
      MeasureTheory.measureReal_union_le upper lower
    _ ≤
        Real.exp (-(typeCount : Real) / 20000000000) +
          Real.exp (-(typeCount : Real) / 20000000000) := by
      apply add_le_add
      · exact measure_centeredCharacterSum_ge_le
          r typeCount ell frequency hfrequency
      · exact measure_centeredCharacterSum_le_neg_le
          r typeCount ell frequency hfrequency
    _ = 2 * Real.exp (-(typeCount : Real) / 20000000000) := by
      ring
end QEC.Coding.FiberBundle.TwistGraph

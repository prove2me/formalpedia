-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.measure_groupedHHO20LightFailure_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:20:44.389547+00:00
-- url     : https://prove2.me/submissions/9b891aa5-fed0-45f7-973b-73c2d5428811

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_groupedLightFailure_subset_iUnion_badAt
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_groupedLightBadAt_le_pow
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_lightFailureIndex_pow_totalWeight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample | ¬ HasGroupedHHO20LightChecks
          (r := r) (typeCount := typeCount) Delta sample} ≤
      typeCount *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) := by
  let badAt : LightFailureIndex r typeCount → Set (Sample r) :=
    groupedLightBadAt r Delta typeCount
  calc
    _ ≤
        (distribution r Delta (by omega)).toMeasure.real
          (⋃ index : LightFailureIndex r typeCount, badAt index) :=
      measureReal_mono
        (groupedLightFailure_subset_iUnion_badAt
          r Delta typeCount)
    _ ≤
        ∑ index : LightFailureIndex r typeCount,
          (distribution r Delta (by omega)).toMeasure.real
            (badAt index) :=
      measureReal_iUnion_fintype_le badAt
    _ ≤
        ∑ index : LightFailureIndex r typeCount,
          (Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (HammingWeight index.2.1.1 +
                HammingWeight index.2.1.2) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact measure_groupedLightBadAt_le_pow
        r Delta typeCount hr hDeltaHalf hTypeDvd index
    _ = _ :=
      sum_lightFailureIndex_pow_totalWeight r typeCount
        (Real.exp
          (-(Delta : Real) / (200 * typeCount)))
end QEC.Coding.FiberBundle.RandomPartition

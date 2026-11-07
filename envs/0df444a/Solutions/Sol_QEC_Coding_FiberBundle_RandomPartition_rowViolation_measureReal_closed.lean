-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:44:33.350481+00:00
-- url     : https://prove2.me/submissions/b949ad76-3927-47ed-87c4-7c8e97634eb8

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_product_localPairMean_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} =
      (1 -
        (1 -
          (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
            HammingWeight (y + z) *
        (1 -
          2 * (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
            pairOverlapCount y z) / 2 := by
  rw [rowViolation_measureReal r Delta hDelta y z,
    product_localPairMean_eq r Delta y z]
end QEC.Coding.FiberBundle.RandomPartition

-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_linear_of_light
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:56:04.675439+00:00
-- url     : https://prove2.me/submissions/8a4a399c-8bca-43a2-bccd-07ec7d33abf9

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal_ge_linear

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hy : Delta * HammingWeight y ≤ 4 * (4 * r))
    (hz : Delta * HammingWeight z ≤ 4 * (4 * r)) :
    (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z) / 25 ≤
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  apply rowViolation_measureReal_ge_linear r Delta hr hDeltaHalf y z
  calc
    Delta * (HammingWeight y + HammingWeight z) =
        Delta * HammingWeight y + Delta * HammingWeight z := by
      exact Nat.mul_add _ _ _
    _ ≤ 4 * (4 * r) + 4 * (4 * r) := Nat.add_le_add hy hz
    _ = 32 * r := by omega
end QEC.Coding.FiberBundle.RandomPartition

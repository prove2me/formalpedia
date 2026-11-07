-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:47:25.874205+00:00
-- url     : https://prove2.me/submissions/76f154f3-a8ea-4a7f-900c-f7f3efa5e8d7

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal_closed
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hammingWeight_add_eq_add_two_pairOverlapCount
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_xorOverlapCharacterProduct_le_exp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hpHalf :
      (RandomBase.incidenceProbability (4 * r) Delta).toReal ≤
        1 / 2) :
    (1 -
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z))) / 2 ≤
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  have hweight :
      (HammingWeight y : Real) + HammingWeight z =
        (HammingWeight (y + z) : Real) +
          2 * (pairOverlapCount y z : Real) := by
    exact_mod_cast hammingWeight_add_eq_add_two_pairOverlapCount y z
  have hcharacter :
      (1 - p) ^ HammingWeight (y + z) *
          (1 - 2 * p) ^ pairOverlapCount y z ≤
        Real.exp
          (-p * ((HammingWeight y : Real) + HammingWeight z)) := by
    rw [hweight]
    exact xorOverlapCharacterProduct_le_exp p
      (HammingWeight (y + z)) (pairOverlapCount y z) hpHalf
  rw [rowViolation_measureReal_closed r Delta hDelta y z]
  change
    (1 -
      Real.exp
        (-p * ((HammingWeight y : Real) + HammingWeight z))) / 2 ≤
      (1 -
        (1 - p) ^ HammingWeight (y + z) *
          (1 - 2 * p) ^ pairOverlapCount y z) / 2
  linarith
end QEC.Coding.FiberBundle.RandomPartition

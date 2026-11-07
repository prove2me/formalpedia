-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.integral_paritySign_rowPairSyndrome_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:42:58.743234+00:00
-- url     : https://prove2.me/submissions/a4ee8206-b57b-49f0-b084-5660b1b29953

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_paritySign_rowPairSyndrome
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_product_localPairMean_eq
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
    (∫ row,
        RandomBase.paritySign (rowPairSyndrome row y z) ∂
          (rowDistribution r Delta hDelta).toMeasure) ≤
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z)) := by
  let p : Real :=
    (RandomBase.incidenceProbability (4 * r) Delta).toReal
  rw [integral_paritySign_rowPairSyndrome r Delta hDelta y z,
    product_localPairMean_eq r Delta y z]
  have hweight :
      (HammingWeight y : Real) + HammingWeight z =
        (HammingWeight (y + z) : Real) +
          2 * (pairOverlapCount y z : Real) := by
    exact_mod_cast hammingWeight_add_eq_add_two_pairOverlapCount y z
  rw [hweight]
  exact xorOverlapCharacterProduct_le_exp p
    (HammingWeight (y + z)) (pairOverlapCount y z) hpHalf
end QEC.Coding.FiberBundle.RandomPartition

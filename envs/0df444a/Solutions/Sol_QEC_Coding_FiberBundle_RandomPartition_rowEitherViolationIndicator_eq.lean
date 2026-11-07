-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rowEitherViolationIndicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:37:12.970194+00:00
-- url     : https://prove2.me/submissions/d9d989b0-630d-4bb0-8183-14196316c553

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowPairSyndrome_add
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_zmod2_eq_one_of_ne_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    {r : Nat}
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (row : RowSample r) :
    rowEitherViolationIndicator x outWord inWord row =
      (3 -
        RandomBase.paritySign
          (rowPairSyndrome row x outWord) -
        RandomBase.paritySign
          (rowPairSyndrome row inWord x) -
        RandomBase.paritySign
          (rowPairSyndrome row (x + inWord) (outWord + x))) / 4 := by
  let first := rowPairSyndrome row x outWord
  let second := rowPairSyndrome row inWord x
  have hsum :
      first + second =
        rowPairSyndrome row (x + inWord) (outWord + x) :=
    rowPairSyndrome_add row x outWord inWord
  change
    (if first ≠ 0 ∨ second ≠ 0 then 1 else 0) =
      (3 - RandomBase.paritySign first -
        RandomBase.paritySign second -
        RandomBase.paritySign
          (rowPairSyndrome row (x + inWord) (outWord + x))) / 4
  rw [← hsum]
  by_cases hFirst : first = 0
  · by_cases hSecond : second = 0
    · norm_num [hFirst, hSecond, RandomBase.paritySign]
    · rw [RandomBase.zmod2_eq_one_of_ne_zero second hSecond]
      norm_num [hFirst, RandomBase.paritySign]
  · rw [RandomBase.zmod2_eq_one_of_ne_zero first hFirst]
    by_cases hSecond : second = 0
    · norm_num [hSecond, RandomBase.paritySign]
    · rw [RandomBase.zmod2_eq_one_of_ne_zero second hSecond]
      have htwo : (1 + 1 : ZMod 2) = 0 := by decide
      rw [htwo]
      norm_num [RandomBase.paritySign]
end QEC.Coding.FiberBundle.RandomPartition

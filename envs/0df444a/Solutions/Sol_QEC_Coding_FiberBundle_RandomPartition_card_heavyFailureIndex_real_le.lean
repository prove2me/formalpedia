-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.card_heavyFailureIndex_real_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:43:02.855212+00:00
-- url     : https://prove2.me/submissions/3ddabe0a-537e-45e0-99a1-b479b0af3720

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_card_heavyFailureIndex
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_card_lightNeighborWord_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount : Nat) (hDelta : 0 < Delta) :
    (Fintype.card (HeavyFailureIndex r Delta typeCount) : Real) ≤
      (2 : Real) ^ (4 * r) *
        ((2 : Real) ^ typeCount *
          (((1 + 1 / (Delta : Real)) ^ (4 * r) *
              (Delta : Real) ^ ((8 * r) / Delta)) ^ typeCount *
            ((1 + 1 / (Delta : Real)) ^ (4 * r) *
              (Delta : Real) ^ ((8 * r) / Delta)) ^ typeCount)) := by
  rw [card_heavyFailureIndex]
  push_cast
  gcongr <;> exact card_lightNeighborWord_le r Delta hDelta
end QEC.Coding.FiberBundle.RandomPartition

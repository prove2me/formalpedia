-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.baseSample_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:19:01.356363+00:00
-- url     : https://prove2.me/submissions/cae4463b-2a5b-4094-aee5-bb2c8c940d35

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    {r : Nat} (sample : Sample r)
    (a : Fin (3 * r)) (b : Fin (4 * r)) :
    baseSample sample (a, b) = sample a b false := by
  rfl
end QEC.Coding.FiberBundle.RandomPartition

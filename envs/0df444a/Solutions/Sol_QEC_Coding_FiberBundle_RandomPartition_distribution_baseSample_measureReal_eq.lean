-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.distribution_baseSample_measureReal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:38:49.460102+00:00
-- url     : https://prove2.me/submissions/bc2183c5-7947-4b42-9f97-7a646ae5e7a4

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_baseSample_hasLaw

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (event : RandomBase.Sample r → Prop) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | event (baseSample sample)} =
      (RandomBase.distribution r Delta hDelta).toMeasure.real
        {base | event base} := by
  exact
    (distribution_baseSample_hasLaw
      r Delta hDelta).measureReal_eq MeasurableSet.of_discrete
end QEC.Coding.FiberBundle.RandomPartition

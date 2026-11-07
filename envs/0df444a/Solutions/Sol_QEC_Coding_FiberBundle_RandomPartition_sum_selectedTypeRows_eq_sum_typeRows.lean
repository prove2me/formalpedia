-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.sum_selectedTypeRows_eq_sum_typeRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:35:59.604766+00:00
-- url     : https://prove2.me/submissions/5e28f9dd-4c2e-4769-860f-bbcaa47f4301

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
    {r typeCount : Nat} [NeZero typeCount]
    (types : Finset (Fin typeCount))
    (f : Fin (3 * r) → Real) :
    (∑ a ∈ selectedTypeRows r typeCount types, f a) =
      ∑ τ ∈ types, ∑ a ∈ typeRows r typeCount τ, f a := by
  unfold selectedTypeRows typeRows
  exact
    (Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ : Finset (Fin (3 * r))) types
      (RandomTwist.checkType typeCount) f).symm
end QEC.Coding.FiberBundle.RandomPartition

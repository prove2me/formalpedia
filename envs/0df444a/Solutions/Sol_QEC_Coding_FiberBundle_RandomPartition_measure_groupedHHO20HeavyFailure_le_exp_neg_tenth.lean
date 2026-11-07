-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.measure_groupedHHO20HeavyFailure_le_exp_neg_tenth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:06:09.123983+00:00
-- url     : https://prove2.me/submissions/4500d657-b46b-4e39-aa8f-1b6b63c0d86f

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_groupedHHO20HeavyFailure_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_heavyFailureUnionTerm_le_exp_neg_tenth

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          ¬TwistGraph.HasHHO20HeavyChecks Delta
            (baseSample sample) (twistSample sample typeShifts)} ≤
      Real.exp (-(r : Real) / 10) := by
  exact
    (measure_groupedHHO20HeavyFailure_le
      r Delta typeCount ell hr hDeltaHalf hTypeDvd typeShifts).trans
      (heavyFailureUnionTerm_le_exp_neg_tenth
        r Delta typeCount hDelta hDeltaOne hTypeSmall hScale)
end QEC.Coding.FiberBundle.RandomPartition

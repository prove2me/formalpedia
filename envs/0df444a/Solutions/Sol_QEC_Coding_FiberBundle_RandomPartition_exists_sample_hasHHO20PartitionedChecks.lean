-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.exists_sample_hasHHO20PartitionedChecks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:32:44.175506+00:00
-- url     : https://prove2.me/submissions/a4d56e1b-47cd-4628-b501-cc36a0e04884

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_sample_hasGroupedHHO20PartitionedChecks
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hasHHO20PartitionedChecks_of_hasGrouped

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 7 ≤ r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (hLightLogScale :
      200 * (typeCount : Real) *
          Real.log (32 * r * typeCount : Nat) <
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    ∃ sample : Sample r,
      TwistGraph.HasHHO20PartitionedChecks Delta
        (baseSample sample) (twistSample sample typeShifts) := by
  obtain ⟨sample, hsample⟩ :=
    exists_sample_hasGroupedHHO20PartitionedChecks
      r Delta typeCount ell hr hDeltaHalf hTypeDvd
      hDelta hDeltaOne hTypeSmall hHeavyScale
      hLightLogScale typeShifts
  exact
    ⟨sample,
      hasHHO20PartitionedChecks_of_hasGrouped
        sample typeShifts hsample⟩
end QEC.Coding.FiberBundle.RandomPartition

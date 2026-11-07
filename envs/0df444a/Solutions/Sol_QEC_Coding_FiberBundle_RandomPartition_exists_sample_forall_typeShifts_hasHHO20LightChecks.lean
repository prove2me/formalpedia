-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.exists_sample_forall_typeShifts_hasHHO20LightChecks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:40:22.679551+00:00
-- url     : https://prove2.me/submissions/187797c7-8b33-498b-b3c7-bf13711b321b

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_sample_hasGroupedHHO20LightChecks
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hasHHO20LightChecks_of_hasGrouped

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hNumeric :
      (typeCount : Real) *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) < 1) :
    ∃ sample : Sample r,
      ∀ typeShifts : Fin typeCount → Fin (ell - 1),
        TwistGraph.HasHHO20LightChecks Delta
          (baseSample sample) (twistSample sample typeShifts) := by
  obtain ⟨sample, hGrouped⟩ :=
    exists_sample_hasGroupedHHO20LightChecks
      r Delta typeCount hr hDeltaHalf hTypeDvd hNumeric
  exact ⟨sample, fun typeShifts =>
    hasHHO20LightChecks_of_hasGrouped
      sample typeShifts hGrouped⟩
end QEC.Coding.FiberBundle.RandomPartition

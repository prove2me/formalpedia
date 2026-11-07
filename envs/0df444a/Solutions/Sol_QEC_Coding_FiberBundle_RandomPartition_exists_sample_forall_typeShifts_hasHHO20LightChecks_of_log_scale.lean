-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.exists_sample_forall_typeShifts_hasHHO20LightChecks_of_log_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:32:25.932445+00:00
-- url     : https://prove2.me/submissions/c2f8c707-e043-400a-afd9-503852e65640

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_light_geometric_union_lt_one_of_exp_lt
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_delta_div_lt_of_log_scale
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_sample_forall_typeShifts_hasHHO20LightChecks

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hLogScale :
      200 * (typeCount : Real) *
          Real.log (16 * r * typeCount : Nat) <
        Delta) :
    ∃ sample : Sample r,
      ∀ typeShifts : Fin typeCount → Fin (ell - 1),
        TwistGraph.HasHHO20LightChecks Delta
          (baseSample sample) (twistSample sample typeShifts) :=
  exists_sample_forall_typeShifts_hasHHO20LightChecks
    r Delta typeCount ell hr hDeltaHalf hTypeDvd
      (light_geometric_union_lt_one_of_exp_lt
        r Delta typeCount hr
          (exp_neg_delta_div_lt_of_log_scale
            r Delta typeCount hr hLogScale))
end QEC.Coding.FiberBundle.RandomPartition

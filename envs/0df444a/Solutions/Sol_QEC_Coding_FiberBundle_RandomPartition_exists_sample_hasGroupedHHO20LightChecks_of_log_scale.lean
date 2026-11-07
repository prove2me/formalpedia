-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.exists_sample_hasGroupedHHO20LightChecks_of_log_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:32:05.59893+00:00
-- url     : https://prove2.me/submissions/38d54980-1eb6-49a6-a2aa-c11d97e79587

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_delta_div_lt_of_log_scale
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_sample_hasGroupedHHO20LightChecks_of_exp_lt

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hLogScale :
      200 * (typeCount : Real) *
          Real.log (16 * r * typeCount : Nat) <
        Delta) :
    ∃ sample : Sample r,
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample :=
  exists_sample_hasGroupedHHO20LightChecks_of_exp_lt
    r Delta typeCount hr hDeltaHalf hTypeDvd
      (exp_neg_delta_div_lt_of_log_scale
        r Delta typeCount hr hLogScale)
end QEC.Coding.FiberBundle.RandomPartition

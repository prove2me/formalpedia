-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.exists_sample_hasGroupedHHO20LightChecks_of_exp_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:40:17.091965+00:00
-- url     : https://prove2.me/submissions/37350899-b906-4876-933a-128b10d288b8

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_sample_hasGroupedHHO20LightChecks
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_light_geometric_union_lt_one_of_exp_lt

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hExpSmall :
      Real.exp
          (-(Delta : Real) / (200 * typeCount)) <
        1 / (16 * r * typeCount : Nat)) :
    ∃ sample : Sample r,
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample :=
  exists_sample_hasGroupedHHO20LightChecks
    r Delta typeCount hr hDeltaHalf hTypeDvd
      (light_geometric_union_lt_one_of_exp_lt
        r Delta typeCount hr hExpSmall)
end QEC.Coding.FiberBundle.RandomPartition

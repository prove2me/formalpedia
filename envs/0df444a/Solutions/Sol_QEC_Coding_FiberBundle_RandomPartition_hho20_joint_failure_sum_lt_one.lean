-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.hho20_joint_failure_sum_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:02:47.546086+00:00
-- url     : https://prove2.me/submissions/153261f6-bcff-45ef-aee4-092ff4236c0c

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_fullyGoodBaseFailureBound_toReal_lt_one_tenth
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_r_div_ten_lt_one_fourth
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_delta_div_lt_inv_thirtyTwo_of_log_scale
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_light_geometric_union_lt_half_of_exp_lt


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 500 ≤ r) (hFive : 5 ∣ r)
    (hDegree :
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) <
        1 / 100)
    (hRank :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 2) <
        1 / 200)
    (hDistance :
      (4 * r : Real) *
          Real.exp (-(3 : Real) * Delta / 28) <
        1 / 200)
    (hExpansion :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 1000) <
        1 / 200)
    (hLightLogScale :
      200 * (typeCount : Real) *
          Real.log (32 * r * typeCount : Nat) <
        Delta) :
    (fullyGoodBaseFailureBound r Delta).toReal +
        ((typeCount : Real) *
            ((1 +
              Real.exp
                (-(Delta : Real) / (200 * typeCount))) ^
                  (8 * r) - 1) +
          Real.exp (-(r : Real) / 10)) <
      1 := by
  have hBase :=
    fullyGoodBaseFailureBound_toReal_lt_one_tenth
      r Delta hr hFive hDegree hRank hDistance hExpansion
  have hrPos : 0 < r := by omega
  have hLight :=
    light_geometric_union_lt_half_of_exp_lt
      r Delta typeCount hrPos
      (exp_neg_delta_div_lt_inv_thirtyTwo_of_log_scale
        r Delta typeCount hrPos hLightLogScale)
  have hHeavy :=
    exp_neg_r_div_ten_lt_one_fourth r (by omega)
  linarith
end QEC.Coding.FiberBundle.RandomPartition

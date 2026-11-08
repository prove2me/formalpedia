-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.hho20_hierarchy_joint_failure_sum_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:30:41.942168+00:00
-- url     : https://prove2.me/submissions/5803f98a-380b-4a0b-a080-485141403fbf

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_joint_failure_sum_lt_one
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_degree_decay_lt
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_rank_decay_lt
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_distance_decay_lt
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_expansion_decay_lt
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_light_log_scale
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_five_dvd_hho20BaseScale

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (s : Nat) (hs : 200 ≤ s) :
    letI : NeZero (hho20TypeCount s) :=
      ⟨hho20TypeCount_ne_zero s (by omega)⟩
    (fullyGoodBaseFailureBound
        (hho20BaseScale s) (hho20DegreeScale s)).toReal +
        ((hho20TypeCount s : Real) *
            ((1 +
              Real.exp
                (-(hho20DegreeScale s : Real) /
                  (200 * hho20TypeCount s))) ^
                    (8 * hho20BaseScale s) - 1) +
          Real.exp (-(hho20BaseScale s : Real) / 10)) <
      1 := by
  letI : NeZero (hho20TypeCount s) :=
    ⟨hho20TypeCount_ne_zero s (by omega)⟩
  exact hho20_joint_failure_sum_lt_one
    (hho20BaseScale s) (hho20DegreeScale s)
    (hho20TypeCount s)
    (hho20_baseScale_ge_five_hundred s hs)
    (five_dvd_hho20BaseScale s)
    (hho20_degree_decay_lt s hs)
    (hho20_rank_decay_lt s hs)
    (hho20_distance_decay_lt s hs)
    (hho20_expansion_decay_lt s hs)
    (hho20_light_log_scale s hs)
end QEC.Coding.FiberBundle.RandomPartition

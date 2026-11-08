-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.two_pow_hundred_lt_exp_hundred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:55:43.797195+00:00
-- url     : https://prove2.me/submissions/b6d9d245-ebc6-4747-9b46-9bed9744a4c5

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution :
    (2 : Real) ^ 100 < Real.exp 100 := by
  have hTwo : (2 : Real) < Real.exp 1 := by
    have h :=
      Real.add_one_lt_exp (by norm_num : (1 : Real) ≠ 0)
    norm_num at h ⊢
    exact h
  calc
    (2 : Real) ^ 100 < (Real.exp 1) ^ 100 :=
      pow_lt_pow_left₀ hTwo (by norm_num) (by norm_num)
    _ = Real.exp 100 := by
      rw [← Real.exp_nat_mul]
      norm_num
end QEC.Coding.FiberBundle.RandomPartition

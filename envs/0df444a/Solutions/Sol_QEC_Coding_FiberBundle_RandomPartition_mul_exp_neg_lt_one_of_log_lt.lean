-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.mul_exp_neg_lt_one_of_log_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:53:15.165969+00:00
-- url     : https://prove2.me/submissions/0b19b5ec-3137-446e-97a4-f84ee992ab46

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    {x y : Real} (hx : 0 < x) (hLog : Real.log x < y) :
    x * Real.exp (-y) < 1 := by
  calc
    x * Real.exp (-y) =
        Real.exp (Real.log x) * Real.exp (-y) := by
      rw [Real.exp_log hx]
    _ = Real.exp (Real.log x - y) := by
      rw [← Real.exp_add]
      congr 1
    _ < Real.exp 0 := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ = 1 := Real.exp_zero
end QEC.Coding.FiberBundle.RandomPartition

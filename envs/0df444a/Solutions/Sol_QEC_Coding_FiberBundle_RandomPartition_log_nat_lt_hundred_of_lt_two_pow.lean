-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.log_nat_lt_hundred_of_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:58:24.964099+00:00
-- url     : https://prove2.me/submissions/2391af37-345e-4d1c-b766-bac39695aa3d

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
import Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_two_pow_hundred_lt_exp_hundred

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (n : Nat) (hn : 0 < n) (hBound : n < 2 ^ 100) :
    Real.log (n : Real) < 100 := by
  rw [Real.log_lt_iff_lt_exp (by exact_mod_cast hn)]
  have hBoundReal : (n : Real) < (2 : Real) ^ 100 := by
    exact_mod_cast hBound
  exact hBoundReal.trans two_pow_hundred_lt_exp_hundred
end QEC.Coding.FiberBundle.RandomPartition

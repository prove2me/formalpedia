-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.exp_neg_r_div_ten_lt_one_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:55:24.543823+00:00
-- url     : https://prove2.me/submissions/647c582c-ee41-4576-b8cd-656d335cc7dc

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r : Nat) (hr : 20 ≤ r) :
    Real.exp (-(r : Real) / 10) < (1 : Real) / 4 := by
  have hLogFour :
      Real.log 4 < (r : Real) / 10 := by
    rw [show (4 : Real) = 2 * 2 by norm_num, Real.log_mul
      (by norm_num : (2 : Real) ≠ 0) (by norm_num : (2 : Real) ≠ 0)]
    have hTwo := Real.log_two_lt_d9
    have hrReal : (20 : Real) ≤ r := by exact_mod_cast hr
    nlinarith
  calc
    Real.exp (-(r : Real) / 10) <
        Real.exp (-Real.log 4) := by
      apply Real.exp_lt_exp.mpr
      linarith
    _ = (1 : Real) / 4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 4)]
      rw [one_div]
end QEC.Coding.FiberBundle.RandomPartition

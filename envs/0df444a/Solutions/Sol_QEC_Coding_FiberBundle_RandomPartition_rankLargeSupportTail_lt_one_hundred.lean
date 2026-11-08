-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.rankLargeSupportTail_lt_one_hundred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:55:11.55619+00:00
-- url     : https://prove2.me/submissions/c54dbb7b-e6cd-42e7-ac66-14a6e3bd964e

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r : Nat) (hr : 100 ≤ r) :
    (2 : Real) ^ (3 * r) *
        ((4 : Real) / 7) ^ (4 * r) <
      1 / 100 := by
  calc
    (2 : Real) ^ (3 * r) *
          ((4 : Real) / 7) ^ (4 * r) =
        ((2048 : Real) / 2401) ^ r := by
      rw [pow_mul, pow_mul, ← mul_pow]
      norm_num
    _ ≤ ((9 : Real) / 10) ^ r := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
    _ ≤ ((9 : Real) / 10) ^ 100 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
    _ < 1 / 100 := by norm_num
end QEC.Coding.FiberBundle.RandomPartition

-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomPartition.distanceLargeSupportTail_lt_one_hundred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:55:13.246379+00:00
-- url     : https://prove2.me/submissions/f964c7d0-4870-42e4-8c21-1dbd229bfae6

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
namespace QEC.Coding.FiberBundle.RandomPartition
theorem _root_.solution
    (r : Nat) (hr : 500 ≤ r) (hFive : 5 ∣ r) :
    ((3 : Real) ^ ((4 * r) / 5) *
        ((4 : Real) / 3) ^ (4 * r)) *
        ((172 : Real) / 343) ^ (3 * r) <
      1 / 100 := by
  obtain ⟨q, rfl⟩ := hFive
  have hq : 100 ≤ q := by omega
  have hFour : (4 * (5 * q)) / 5 = 4 * q := by omega
  have hTwenty : 4 * (5 * q) = 20 * q := by omega
  have hFifteen : 3 * (5 * q) = 15 * q := by omega
  calc
    ((3 : Real) ^ ((4 * (5 * q)) / 5) *
          ((4 : Real) / 3) ^ (4 * (5 * q))) *
          ((172 : Real) / 343) ^ (3 * (5 * q)) =
        (((3 : Real) ^ 4 *
          ((4 : Real) / 3) ^ 20) *
          ((172 : Real) / 343) ^ 15) ^ q := by
      rw [hFour, hTwenty, hFifteen, pow_mul, pow_mul, pow_mul,
        ← mul_pow, ← mul_pow]
    _ ≤ ((9 : Real) / 10) ^ q := by
      exact pow_le_pow_left₀ (by positivity) (by norm_num) q
    _ ≤ ((9 : Real) / 10) ^ 100 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
    _ < 1 / 100 := by norm_num
end QEC.Coding.FiberBundle.RandomPartition

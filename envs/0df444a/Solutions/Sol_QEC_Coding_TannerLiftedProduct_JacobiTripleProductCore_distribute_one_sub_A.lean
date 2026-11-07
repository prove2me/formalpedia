-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.distribute_one_sub_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:30.941133+00:00
-- url     : https://prove2.me/submissions/9071ef10-c0ca-4512-b2b9-9005404e98c4

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n : ℕ) :
    (1 - A) * ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 =
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 +
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 := by
  rw [show (1 - A) = 1 + (-A) by ring, add_mul, one_mul]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [show (k + 1).choose 2 = k + k.choose 2 by simp [Nat.choose_succ_succ],
        pow_add, ← pow_add, pow_succ']
    ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

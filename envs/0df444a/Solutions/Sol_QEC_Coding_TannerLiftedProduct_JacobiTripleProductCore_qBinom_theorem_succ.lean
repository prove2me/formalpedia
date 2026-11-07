-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_theorem_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:23.748402+00:00
-- url     : https://prove2.me/submissions/0a7a6030-430f-4946-b264-061c456e9313

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_distribute_one_sub_A
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_combine_sums

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n : ℕ)
    (ih : ∀ (A' : R), qPoch A' Q n =
      ∑ k ∈ Finset.range (n + 1), qBinom Q n k * (-A') ^ k * Q ^ k.choose 2) :
    qPoch A Q (n + 1) =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by
  rw [qPoch_succ, ih (A * Q)]
  have key : ∀ k, qBinom Q n k * (-(A * Q)) ^ k * Q ^ k.choose 2 =
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 := by
    intro k
    rw [show -(A * Q) = -A * Q from (neg_mul A Q).symm, mul_pow]
    ring
  simp_rw [key]
  rw [distribute_one_sub_A, combine_sums]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

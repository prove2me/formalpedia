-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.reassemble_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:34.459508+00:00
-- url     : https://prove2.me/submissions/3856240d-bb2f-4df3-b194-dc25d02f1939

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n : ℕ) :
    1 + ∑ k ∈ Finset.range n,
      qBinom Q (n + 1) (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 +
    (-A) ^ (n + 1) * Q ^ (n + 1).choose 2 =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by
  rw [Finset.sum_range_succ]
  simp only [qBinom_self, one_mul]
  rw [Finset.sum_range_succ']
  simp only [qBinom, pow_zero, one_mul]
  norm_num
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.split_S1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:31.854394+00:00
-- url     : https://prove2.me/submissions/1c975264-ebe9-4680-929a-3ae78a9ad775

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 =
    1 + ∑ k ∈ Finset.range n,
      qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2 := by
  rw [Finset.sum_range_succ', show qBinom Q n 0 * (-A) ^ 0 * Q ^ 0 * Q ^ (0 : ℕ).choose 2 = 1
    by simp [qBinom], add_comm]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

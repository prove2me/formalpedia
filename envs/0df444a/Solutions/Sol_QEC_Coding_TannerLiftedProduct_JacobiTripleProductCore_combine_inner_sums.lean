-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.combine_inner_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:31.309323+00:00
-- url     : https://prove2.me/submissions/5cc7e3b1-f12b-4384-a732-5e8209a8fe97

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_combine_summand

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2) +
    (∑ k ∈ Finset.range n,
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2) =
    ∑ k ∈ Finset.range n,
      qBinom Q (n + 1) (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => combine_summand A Q n k
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

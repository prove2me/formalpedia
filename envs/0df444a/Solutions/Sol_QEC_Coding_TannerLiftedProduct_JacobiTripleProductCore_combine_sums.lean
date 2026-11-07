-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.combine_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:45:51.54383+00:00
-- url     : https://prove2.me/submissions/806ad8a3-e0c8-486c-9e76-0184dd75fe1b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_split_S1
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_split_S2
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_combine_inner_sums
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_reassemble_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ k * Q ^ k * Q ^ k.choose 2 +
    ∑ k ∈ Finset.range (n + 1),
      qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2 =
    ∑ k ∈ Finset.range (n + 2), qBinom Q (n + 1) k * (-A) ^ k * Q ^ k.choose 2 := by
  rw [split_S1, split_S2]
  set S1' := ∑ k ∈ Finset.range n,
    qBinom Q n (k + 1) * (-A) ^ (k + 1) * Q ^ (k + 1) * Q ^ (k + 1).choose 2
  set S2' := ∑ k ∈ Finset.range n,
    qBinom Q n k * (-A) ^ (k + 1) * Q ^ (k + 1).choose 2
  set last := (-A) ^ (n + 1) * Q ^ (n + 1).choose 2
  rw [show 1 + S1' + (S2' + last) = 1 + (S1' + S2') + last by ring, combine_inner_sums]
  exact reassemble_sum A Q n
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

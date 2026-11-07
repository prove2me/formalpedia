-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qbinom_sum_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:42.580685+00:00
-- url     : https://prove2.me/submissions/6c702a17-7513-497b-acb2-6027874a42c6

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exponent_simp

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (-(-x * q)) ^ k * (q ^ 2) ^ k.choose 2 =
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (q ^ (k ^ 2) * x ^ k) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_assoc, exponent_simp]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

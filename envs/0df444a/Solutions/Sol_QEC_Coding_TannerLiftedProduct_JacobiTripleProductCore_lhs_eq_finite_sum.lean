-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_eq_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:50:37.814354+00:00
-- url     : https://prove2.me/submissions/589ed82f-f770-4268-9f43-300425a46dd8

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_mul_tsum_eq_tsum_mul
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_rhs_eq_finite_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m : ℕ) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (qPochhammerInf (q ^ 2) (q ^ 2) *
        (q ^ (k ^ 2) * x ^ k *
          PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m := by
  rw [mul_tsum_eq_tsum_mul x]
  exact rhs_eq_finite_sum x m
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

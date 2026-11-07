-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.distribute_mul_tsum_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:52:05.409903+00:00
-- url     : https://prove2.me/submissions/1466c187-91b7-4aa1-84b2-944d5fc24fbf

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_rhs_eq_finite_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_lhs_eq_finite_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m : ℕ) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m := by
  rw [lhs_eq_finite_sum, rhs_eq_finite_sum]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

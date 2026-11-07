-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.product_sum_expansion_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:18.467793+00:00
-- url     : https://prove2.me/submissions/cc764f66-20d7-43ee-9730-b4879b2f0203

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_euler_product
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_distribute_mul_tsum_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_coeff_congr_of_per_term

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m : ℕ) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-x * q) (q ^ 2) : R).coeff m =
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) : R).coeff m := by
  letI := piTop
  rw [euler_product x, distribute_mul_tsum_coeff x m]
  exact tsum_coeff_congr_of_per_term x m
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

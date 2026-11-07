-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.termwise_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:47.198483+00:00
-- url     : https://prove2.me/submissions/96834bf2-626e-4e5f-9fae-c3fc83358f09

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_conv_sum_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m k : ℕ) (hk : k ≤ m) :
    (qBinom (q ^ 2) (2 * m + 1) k * (q ^ (k ^ 2) * x ^ k) : R).coeff m =
    (q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  rw [mul_comm (q ^ (k ^ 2) * x ^ k), PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  exact conv_sum_eq x m k hk
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

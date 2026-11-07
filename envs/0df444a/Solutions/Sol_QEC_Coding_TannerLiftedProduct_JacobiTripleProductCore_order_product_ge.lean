-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_product_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:09:50.448709+00:00
-- url     : https://prove2.me/submissions/129e1d1a-fa38-4ac0-b064-13686143fbae

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_q_pow_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (k : ℕ) :
    (k ^ 2 : ℕ∞) ≤ (q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).order := by
  rw [mul_assoc]
  calc (k ^ 2 : ℕ∞) ≤ (q ^ (k ^ 2) : R).order := order_q_pow_ge _
    _ ≤ (q ^ (k ^ 2) : R).order + ((x ^ k : R).order +
        (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).order) :=
        le_add_of_nonneg_right (by positivity)
    _ ≤ _ := le_trans (by
        gcongr
        exact PowerSeries.le_order_mul ..) (PowerSeries.le_order_mul ..)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

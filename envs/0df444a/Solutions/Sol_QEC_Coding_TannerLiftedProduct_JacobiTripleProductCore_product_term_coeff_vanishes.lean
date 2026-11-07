-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.product_term_coeff_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:46.209481+00:00
-- url     : https://prove2.me/submissions/90dee792-1c49-45ec-8c43-4c01ca516abb

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_product_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_mul_eq_zero_of_order_gt

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m k : ℕ) (hk : m < k) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m = 0 := by
  apply coeff_mul_eq_zero_of_order_gt
  right
  calc (m : ℕ∞) < k := by exact_mod_cast hk
    _ ≤ k ^ 2 := by exact_mod_cast Nat.le_self_pow (by omega) k
    _ ≤ _ := order_product_ge x k
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

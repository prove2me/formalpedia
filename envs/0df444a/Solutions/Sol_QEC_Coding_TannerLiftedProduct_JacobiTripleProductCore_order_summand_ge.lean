-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_summand_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:50:34.054417+00:00
-- url     : https://prove2.me/submissions/d61cb5ac-79c6-43f1-bacd-c7f8c71ecca7

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_isUnit_C_T

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k ℓ : ℕ) :
    ((k + ℓ) ^ 2 + ℓ : ℕ∞) ≤
      (PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
       ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order := by
  calc ((k + ℓ) ^ 2 + ℓ : ℕ∞)
      ≤ 0 + (0 + (q ^ ((k + ℓ) ^ 2 + ℓ) : R).order) := by simp
    _ ≤ (PowerSeries.C (LaurentPolynomial.T (k : ℤ)) : R).order +
        (((-1 : R) ^ ℓ).order + (q ^ ((k + ℓ) ^ 2 + ℓ) : R).order) := by
          rw [PowerSeries.order_zero_of_unit (isUnit_C_T k),
              PowerSeries.order_zero_of_unit ((isUnit_one : IsUnit (1 : R)).neg.pow ℓ)]
    _ ≤ _ := le_trans (by gcongr; exact PowerSeries.order_mul_ge _ _)
        (le_trans (PowerSeries.order_mul_ge _ _)
          (le_trans (le_add_of_nonneg_right zero_le) (PowerSeries.le_order_mul ..)))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

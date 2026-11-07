-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_product_term_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:29:29.288798+00:00
-- url     : https://prove2.me/submissions/e43e69e5-75d5-430b-b624-fc414231cd04

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_first_factor_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_E_term_ge_1

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m : ℤ) (ℓ : ℕ) :
    (m.natAbs ^ 2 + ℓ : ℕ∞) ≤
      ((PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) *
       ((-(q * aI)) ^ ℓ * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1)).order := by
  calc (m.natAbs ^ 2 + ℓ : ℕ∞)
      = (m.natAbs ^ 2 : ℕ∞) + (ℓ : ℕ∞) := by norm_cast
    _ ≤ (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2 : R).order +
        ((-(q * aI)) ^ ℓ * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 : R).order :=
        add_le_add (order_first_factor_ge m) (order_E_term_ge_1 ℓ)
    _ ≤ _ := PowerSeries.order_mul_ge _ _
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

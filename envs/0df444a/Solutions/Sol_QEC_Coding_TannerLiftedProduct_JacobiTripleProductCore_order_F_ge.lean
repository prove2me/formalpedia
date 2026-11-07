-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_F_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:14:27.877212+00:00
-- url     : https://prove2.me/submissions/75f72b6f-bc00-4161-bfd9-e8db8c276d6b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_q_pow_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (z : ℤ) (ℓ : ℕ) :
    ((z + ↑ℓ).natAbs ^ 2 + ℓ : ℕ∞) ≤ (F (z, ℓ)).order := by
  set m := (z + ↑ℓ).natAbs ^ 2 + ℓ
  calc (m : ℕ∞) ≤ (q ^ m : R).order := order_q_pow_ge m
    _ ≤ ((-1 : R) ^ ℓ * q ^ m).order := le_trans le_add_self (PowerSeries.order_mul_ge _ _)
    _ ≤ (PowerSeries.C (LaurentPolynomial.T z) *
        ((-1 : R) ^ ℓ * q ^ m)).order := le_trans le_add_self (PowerSeries.order_mul_ge _ _)
    _ ≤ _ := le_trans (le_add_of_nonneg_right zero_le) (PowerSeries.order_mul_ge _ _)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

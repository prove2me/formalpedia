-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_neg_q_aI_pow_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:52:07.18083+00:00
-- url     : https://prove2.me/submissions/9debbc5f-3f42-44d9-9b24-dac116b13382

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_q_mul_aI

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (ℓ : ℕ) :
    (ℓ : ℕ∞) ≤ ((-(q * aI)) ^ ℓ : R).order := by
  calc (ℓ : ℕ∞) = ℓ • (1 : ℕ∞) := (nsmul_one ℓ).symm
    _ ≤ ℓ • ((-(q * aI) : R).order) := by
        apply nsmul_le_nsmul_right
        rw [ENat.one_le_iff_ne_zero, PowerSeries.order_neg,
            PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]
        exact constantCoeff_q_mul_aI
    _ ≤ ((-(q * aI)) ^ ℓ : R).order := PowerSeries.le_order_pow _ _
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

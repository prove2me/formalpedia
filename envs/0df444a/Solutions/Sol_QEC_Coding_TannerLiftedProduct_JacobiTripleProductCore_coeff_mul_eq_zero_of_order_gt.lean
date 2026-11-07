-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_mul_eq_zero_of_order_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:12:14.475852+00:00
-- url     : https://prove2.me/submissions/27fef4df-a8e1-4223-90f6-e5f3716b83c0

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {d : ℕ} {φ ψ : R}
    (h : (d : ℕ∞) < φ.order ∨ (d : ℕ∞) < ψ.order) :
    (PowerSeries.coeff d) (φ * ψ) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  calc (d : ℕ∞) < φ.order + ψ.order := by
        rcases h with h | h
        · exact lt_of_lt_of_le h (le_add_of_nonneg_right zero_le)
        · exact lt_of_lt_of_le h (le_add_of_nonneg_left zero_le)
    _ ≤ (φ * ψ).order := PowerSeries.order_mul_ge φ ψ
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_coeff_mul_pow_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:38.286288+00:00
-- url     : https://prove2.me/submissions/ec8af0bf-6b86-4598-96a1-75263c6c95ca

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {x : R} (hx : x.constantCoeff = 0) (p : S) (n : ℕ) :
    (n : ℕ∞) ≤ ((p.coeff n) * x ^ n).order := by
  have h1 : (1 : ℕ∞) ≤ x.order :=
    ENat.one_le_iff_ne_zero.mpr (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mpr hx)
  calc (n : ℕ∞) = n • (1 : ℕ∞) := by simp
    _ ≤ n • x.order := nsmul_le_nsmul_right h1 n
    _ ≤ (x ^ n).order := PowerSeries.le_order_pow x n
    _ ≤ _ := le_trans le_add_self (PowerSeries.order_mul_ge _ _)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

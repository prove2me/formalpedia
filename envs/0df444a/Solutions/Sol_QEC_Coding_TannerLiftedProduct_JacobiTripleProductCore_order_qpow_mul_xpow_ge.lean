-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_qpow_mul_xpow_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:11:18.1564+00:00
-- url     : https://prove2.me/submissions/c475fdde-fcba-46ca-bf5d-7f2a9e7cb2be

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_q_pow_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (k : ℕ) :
    (k ^ 2 : ℕ∞) ≤ (q ^ (k ^ 2) * x ^ k : R).order :=
  le_trans (le_trans (order_q_pow_ge _) (le_add_of_nonneg_right zero_le)) (PowerSeries.order_mul_ge _ _)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

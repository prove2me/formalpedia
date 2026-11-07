-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_E_term_ge_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:54:13.800142+00:00
-- url     : https://prove2.me/submissions/78dcb363-0ace-40cd-94d6-49a8f67e5aa7

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_neg_q_aI_pow_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (ℓ : ℕ) :
    (ℓ : ℕ∞) ≤ ((-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order :=
  le_trans
    (le_trans (by rw [add_zero]) (add_le_add (order_neg_q_aI_pow_ge ℓ) zero_le))
    (PowerSeries.order_mul_ge _ _)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

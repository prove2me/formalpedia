-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_G_term_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:14:32.364811+00:00
-- url     : https://prove2.me/submissions/59da5a20-238c-4aed-bd8f-2801db7e3bd4

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_q_pow_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) :
    (N_exp j ℓ : ℕ∞) ≤
    ((-1 : R) ^ ℓ * q ^ N_exp j ℓ *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1).order := by
  calc (N_exp j ℓ : ℕ∞)
      = 0 + ↑(N_exp j ℓ) := by simp
    _ ≤ ((-1 : R) ^ ℓ).order + (q ^ N_exp j ℓ).order := by
        gcongr
        · exact le_of_eq (PowerSeries.order_zero_of_unit (isUnit_neg_one.pow ℓ)).symm
        · exact order_q_pow_ge _
    _ ≤ ((-1 : R) ^ ℓ * q ^ N_exp j ℓ).order := PowerSeries.le_order_mul _ _
    _ ≤ _ := le_trans (le_add_of_nonneg_right zero_le) (PowerSeries.le_order_mul _ _)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

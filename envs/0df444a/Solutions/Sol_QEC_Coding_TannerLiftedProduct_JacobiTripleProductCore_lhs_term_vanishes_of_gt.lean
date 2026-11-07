-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_term_vanishes_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:23:09.908786+00:00
-- url     : https://prove2.me/submissions/cd1f34ff-0ea1-4dcf-be7e-01777959121c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_qpow_mul_xpow_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m k : ℕ) (hk : m < k) :
    (qBinom (q ^ 2) (2 * m + 1) k * (q ^ (k ^ 2) * x ^ k) : R).coeff m = 0 := by
  apply PowerSeries.coeff_of_lt_order
  calc (m : ℕ∞) < k ^ 2 := by exact_mod_cast (show m < k ^ 2 by nlinarith)
    _ ≤ 0 + (k ^ 2 : ℕ∞) := by simp
    _ ≤ (qBinom (q ^ 2) (2 * m + 1) k).order + (q ^ (k ^ 2) * x ^ k : R).order :=
        add_le_add bot_le (order_qpow_mul_xpow_ge x k)
    _ ≤ _ := PowerSeries.order_mul_ge _ _
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

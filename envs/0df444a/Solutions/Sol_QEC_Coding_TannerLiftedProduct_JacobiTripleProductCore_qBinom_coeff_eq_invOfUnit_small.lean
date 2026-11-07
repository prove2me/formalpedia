-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_coeff_eq_invOfUnit_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:39.505739+00:00
-- url     : https://prove2.me/submissions/9e60661f-6084-4ef2-8b1f-9465435fbf90

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tail_mul_inv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_eq_tail_mul_inv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m k i : ℕ) (hk : k ≤ m) (hi : i < k)
    (_him : i ≤ m) :
    (qBinom (q ^ 2) (2 * m + 1) k : R).coeff i =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff i := by
  rw [qBinom_eq_tail_mul_inv (2 * m + 1) k (by omega)]
  exact coeff_tail_mul_inv i k (2 * m + 1) (by omega)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_eq_tail_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:51:53.720555+00:00
-- url     : https://prove2.me/submissions/aa5b696e-938b-48f0-97e6-58fa5084e43a

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_mul_invOfUnit_cancel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_mul_qPoch_k

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (n k : ℕ) (hkn : k ≤ n) :
    qBinom (q ^ 2) n k =
    qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 := by
  have h := qBinom_mul_qPoch_k n k hkn
  rw [show qBinom (q ^ 2) n k = qBinom (q ^ 2) n k * qPoch (q ^ 2) (q ^ 2) k *
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 by
    rw [mul_assoc, qPoch_mul_invOfUnit_cancel, mul_one], h]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

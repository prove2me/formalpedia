-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:01.050975+00:00
-- url     : https://prove2.me/submissions/b9643621-bf93-45dc-87e9-90eeb95b9df4

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ__251408f0b858
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_algebraic_identity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_ring_rearrangement

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (Q : R) (n k : ℕ) (hk : k < n)
    (ih1 : qBinom Q n k * qPoch Q Q k * qPoch Q Q (n - k) = qPoch Q Q n)
    (ih2 : qBinom Q n (k + 1) * qPoch Q Q (k + 1) * qPoch Q Q (n - (k + 1)) = qPoch Q Q n) :
    (qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)) *
      (qPoch Q Q k * (1 - Q * Q ^ k)) *
      (qPoch Q Q (n - (k + 1)) * (1 - Q * Q ^ (n - (k + 1)))) =
    qPoch Q Q n * (1 - Q * Q ^ n) := by
  have h_unfold_nk : qPoch Q Q (n - k) =
      qPoch Q Q (n - (k + 1)) * (1 - Q * Q ^ (n - (k + 1))) := by
    rw [show n - k = (n - (k + 1)) + 1 by omega]
    exact qPoch_succ' Q Q (n - (k + 1))
  rw [h_unfold_nk] at ih1
  rw [qPoch_succ' Q Q k] at ih2
  exact ring_rearrangement Q n k (qPoch Q Q n) (qPoch Q Q k) (qPoch Q Q (n - (k + 1)))
    (qBinom Q n k) (qBinom Q n (k + 1)) ih1 ih2 (algebraic_identity Q n k hk)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

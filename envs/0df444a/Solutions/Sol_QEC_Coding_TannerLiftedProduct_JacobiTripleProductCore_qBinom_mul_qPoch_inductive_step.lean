-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch_inductive_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:34.340137+00:00
-- url     : https://prove2.me/submissions/72dbb2c7-d1b0-4338-968c-1df8d2969cc6

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ__251408f0b858
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_mul_qPoch_core

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (Q : R) (n k : ℕ) (hk : k < n)
    (ih1 : qBinom Q n k * qPoch Q Q k * qPoch Q Q (n - k) = qPoch Q Q n)
    (ih2 : qBinom Q n (k + 1) * qPoch Q Q (k + 1) * qPoch Q Q (n - (k + 1)) = qPoch Q Q n) :
    qBinom Q (n + 1) (k + 1) * qPoch Q Q (k + 1) * qPoch Q Q (n - k) = qPoch Q Q (n + 1) := by
  show (qBinom Q n k + Q ^ (k + 1) * qBinom Q n (k + 1)) *
    qPoch Q Q (k + 1) * qPoch Q Q (n - k) = qPoch Q Q (n + 1)
  rw [qPoch_succ' Q Q n, qPoch_succ' Q Q k,
      show n - k = (n - (k + 1)) + 1 by omega, qPoch_succ' Q Q (n - (k + 1))]
  exact qBinom_mul_qPoch_core Q n k hk ih1 ih2
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

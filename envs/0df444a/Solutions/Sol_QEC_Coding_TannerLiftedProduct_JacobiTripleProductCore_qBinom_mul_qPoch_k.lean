-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_mul_qPoch_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:50:02.607971+00:00
-- url     : https://prove2.me/submissions/433c3798-5b57-4465-8d70-90a56eed637c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_split
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_mul_qPoch
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_isUnit_qPoch

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (n k : ℕ) (hkn : k ≤ n) :
    qBinom (q ^ 2) n k * qPoch (q ^ 2) (q ^ 2) k =
    qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k := by
  have h1 := qBinom_mul_qPoch (q ^ 2) n k hkn
  have h2 := qPoch_split (q ^ 2) (q ^ 2) (n - k) k
  rw [Nat.sub_add_cancel hkn] at h2
  rw [h2] at h1
  exact (isUnit_qPoch (n - k)).mul_right_cancel (by linear_combination h1)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

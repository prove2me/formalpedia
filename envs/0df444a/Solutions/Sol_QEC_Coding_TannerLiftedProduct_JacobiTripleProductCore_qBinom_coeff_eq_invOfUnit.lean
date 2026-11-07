-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qBinom_coeff_eq_invOfUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:38.526124+00:00
-- url     : https://prove2.me/submissions/41823591-7bd5-40d2-b617-e67de32abc55

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tail_mul_inv
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qBinom_eq_tail_mul_inv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m k n : ℕ) (_ : k ≤ m) (hn : m + k + 1 ≤ n) :
    (qBinom (q ^ 2) n k : R).coeff m =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  rw [qBinom_eq_tail_mul_inv n k (by omega)]
  exact coeff_tail_mul_inv m k n hn
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

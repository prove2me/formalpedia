-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tail_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:13.00485+00:00
-- url     : https://prove2.me/submissions/b1c2a2c6-a889-4b1c-82eb-5e8a0dc00670

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_mul_of_trunc_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tail_qPoch_coeff_eq_ite

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m k n : ℕ) (hn : m + k + 1 ≤ n) :
    (qPoch (q ^ 2 * (q ^ 2) ^ (n - k)) (q ^ 2) k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m =
    (PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  rw [mul_comm]
  exact coeff_mul_of_trunc_one _ _ _ (tail_qPoch_coeff_eq_ite m k n hn)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

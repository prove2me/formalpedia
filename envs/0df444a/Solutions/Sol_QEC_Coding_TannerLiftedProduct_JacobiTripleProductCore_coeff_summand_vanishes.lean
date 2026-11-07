-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_summand_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:51:58.877692+00:00
-- url     : https://prove2.me/submissions/91ee7a57-8c41-4073-9bc5-b87490f7bc01

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_summand_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k ℓ d : ℕ) (h : d < (k + ℓ) ^ 2 + ℓ) :
    (PowerSeries.coeff d)
      (PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
       ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  exact Nat.cast_lt.mpr h |>.trans_le (order_summand_ge k ℓ)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

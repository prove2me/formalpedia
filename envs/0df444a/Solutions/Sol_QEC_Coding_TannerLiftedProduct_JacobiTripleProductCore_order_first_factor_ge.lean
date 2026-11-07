-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_first_factor_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:15:42.872647+00:00
-- url     : https://prove2.me/submissions/853a4e82-1e40-4212-8b9f-07ba20f26b1b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_isUnit_C_T

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m : ℤ) :
    (m.natAbs ^ 2 : ℕ∞) ≤
      (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2 : R).order := by
  calc (m.natAbs ^ 2 : ℕ∞)
      ≤ 0 + (q ^ m.natAbs ^ 2 : R).order := by simp
    _ ≤ _ := by
      rw [← PowerSeries.order_zero_of_unit (isUnit_C_T m)]
      exact PowerSeries.le_order_mul ..
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

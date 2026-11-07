-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_C_T_mul_q_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:50:38.645195+00:00
-- url     : https://prove2.me/submissions/762b98f9-282d-44c8-bf27-abfb2f364d8c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_first_factor_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) (m : ℤ) (hm : d < m.natAbs ^ 2) :
    (PowerSeries.coeff d) (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  calc (↑d : ℕ∞) < ↑(m.natAbs ^ 2) := by exact_mod_cast hm
    _ ≤ (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2 : R).order :=
        order_first_factor_ge m
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

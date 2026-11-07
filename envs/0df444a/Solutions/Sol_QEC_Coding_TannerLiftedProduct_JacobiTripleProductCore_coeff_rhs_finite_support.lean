-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_rhs_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:51.246554+00:00
-- url     : https://prove2.me/submissions/f9c5781a-cc31-4780-aa00-a54741113354

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_C_T_mul_q_pow_eq_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_natAbs_sq_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (d : ℕ) :
    (Function.support (fun m : ℤ =>
      (PowerSeries.coeff d) (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2))).Finite :=
  (finite_natAbs_sq_le d).subset fun m hm => by
    simp only [Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    exact hm (coeff_C_T_mul_q_pow_eq_zero d m h)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

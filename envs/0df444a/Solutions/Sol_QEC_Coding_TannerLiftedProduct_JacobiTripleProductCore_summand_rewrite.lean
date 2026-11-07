-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:29:05.15382+00:00
-- url     : https://prove2.me/submissions/8c1e3148-cd66-4ea5-945e-fe534df49577

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_a_pow_eq_C_T
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summand_term_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_distribute_into_tsum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) : letI := piTop;
    q ^ (k ^ 2) * a ^ k *
      (∑' ℓ : ℕ, (-1) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ∑' ℓ : ℕ,
      PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by
  letI := piTop
  rw [a_pow_eq_C_T, distribute_into_tsum]
  exact tsum_congr fun ℓ => summand_term_eq k ℓ
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_product_eq_double_sum_over_Z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:26.992742+00:00
-- url     : https://prove2.me/submissions/54a39f5a-b24e-4568-bf2b-aab5739c3152

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_instIsTopologicalSemiringPiTop
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_piTop_T3
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_rhs_terms
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_E_terms
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_product_terms
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summand_rhs_E_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    rhs * (∑' ℓ : ℕ, (-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 - ↑p.2)) *
      ((-1 : R) ^ p.2 * q ^ (p.1.natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by
  letI := piTop
  haveI := piTop_T3
  haveI := instIsTopologicalSemiringPiTop
  show rhs * _ = _
  unfold rhs
  rw [summable_rhs_terms.tsum_mul_tsum summable_E_terms summable_product_terms]
  exact tsum_congr (fun p => summand_rhs_E_eq p.1 p.2)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

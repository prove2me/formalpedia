-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.double_sum_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:12:07.751926+00:00
-- url     : https://prove2.me/submissions/00296985-bdcd-46fb-b01d-180e5b2f2c60

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_rhs_product_eq_double_sum_over_Z
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_reindex_Z_sum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_restrict_Z_to_N

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    rhs * (∑' ℓ : ℕ, (-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by
  letI := piTop
  rw [rhs_product_eq_double_sum_over_Z, reindex_Z_sum, restrict_Z_to_N]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.double_sum_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:01:22.986404+00:00
-- url     : https://prove2.me/submissions/ccd143fa-e46a-4f07-b779-861bd8ea3d7b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_product_sum_expansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_expand_shifted_product
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summand_rewrite
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_sum_interchange

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2) =
    ∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1 := by
  rw [show (-q * a : R) = -a * q by ring, product_sum_expansion a]
  simp_rw [expand_shifted_product]
  letI := piTop
  rw [tsum_congr (fun k => summand_rewrite k), sum_interchange]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

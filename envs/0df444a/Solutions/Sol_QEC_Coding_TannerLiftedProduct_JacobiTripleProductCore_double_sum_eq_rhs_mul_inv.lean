-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.double_sum_eq_rhs_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:16:33.011545+00:00
-- url     : https://prove2.me/submissions/03911a70-ea0a-4616-a31f-e103e2ff4955

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_double_sum_expansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_triple_product_eq_rhs
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_P3

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
    rhs * PowerSeries.invOfUnit (qPochhammerInf (-q * aI) (q ^ 2)) 1 := by
  letI := piTop; rw [← double_sum_expansion]
  calc qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2)
      = _ * qPochhammerInf (-q * aI) (q ^ 2) *
          PowerSeries.invOfUnit (qPochhammerInf (-q * aI) (q ^ 2)) 1 := by
        rw [mul_assoc, PowerSeries.mul_invOfUnit _ _ constantCoeff_P3, mul_one]
    _ = _ := by rw [triple_product_eq_rhs]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

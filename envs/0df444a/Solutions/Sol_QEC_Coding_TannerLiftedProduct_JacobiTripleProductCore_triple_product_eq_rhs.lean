-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.triple_product_eq_rhs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:13:39.437927+00:00
-- url     : https://prove2.me/submissions/c1ce8c50-e516-44b1-a3a5-c129c924ed66

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_euler_inverse
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_double_sum_expansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_q_mul_aI
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_double_sum_factors

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2) *
    qPochhammerInf (-q * aI) (q ^ 2) = rhs := by
  letI := piTop
  rw [double_sum_expansion, double_sum_factors, mul_assoc]
  conv_lhs => rw [show -q * aI = -(q * aI) by ring]
  rw [euler_inverse (q * aI) constantCoeff_q_mul_aI, mul_one]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

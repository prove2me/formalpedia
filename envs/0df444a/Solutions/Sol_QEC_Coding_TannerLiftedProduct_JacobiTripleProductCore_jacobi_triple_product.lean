-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.jacobi_triple_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:42:34.670972+00:00
-- url     : https://prove2.me/submissions/63455617-7955-4561-bef9-a8af25d9f73e

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_double_sum_expansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_P3
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_double_sum_eq_rhs_mul_inv

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : lhs = rhs := by
  unfold lhs
  rw [double_sum_expansion, double_sum_eq_rhs_mul_inv, mul_assoc,
      PowerSeries.invOfUnit_mul _ _ (by rw [constantCoeff_P3]; rfl), mul_one]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

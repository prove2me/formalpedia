-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:29:06.181533+00:00
-- url     : https://prove2.me/submissions/12228374-6800-4c2e-a879-7ebc510449a7

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_function_summable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piUnif;
    Summable (fun p : ℕ × ℕ =>
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℤ)]
  exact coeff_function_summable
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

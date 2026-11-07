-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_rhs_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:29:17.209452+00:00
-- url     : https://prove2.me/submissions/cd78c16b-dfd3-472d-bf29-344332334c41

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_rhs_finite_support

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    Summable (fun m : ℤ => PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) := by
  letI := piTop
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  exact fun d => summable_of_finite_support (coeff_rhs_finite_support d)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

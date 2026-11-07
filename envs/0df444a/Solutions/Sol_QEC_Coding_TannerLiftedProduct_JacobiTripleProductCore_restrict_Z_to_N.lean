-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.restrict_Z_to_N
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:11.903206+00:00
-- url     : https://prove2.me/submissions/ec5c7fe7-c3f2-45cf-b172-aeb2ac6b14e5

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_F_eq_tsum_G

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' p : ℤ × ℕ, PowerSeries.C (LaurentPolynomial.T p.1) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    (∑' p : ℕ × ℕ, PowerSeries.C (LaurentPolynomial.T (↑p.1)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := tsum_F_eq_tsum_G
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

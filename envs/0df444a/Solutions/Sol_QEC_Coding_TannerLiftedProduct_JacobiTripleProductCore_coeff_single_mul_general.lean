-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_single_mul_general
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:29.45514+00:00
-- url     : https://prove2.me/submissions/8ba821ba-dabd-4f38-a93f-f1d089e6e9b9

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (e : ℤ) (c : LaurentPolynomial ℤ) (f : S_hahn) (b : ℤ) :
    (HahnSeries.single e c * f).coeff b = c * f.coeff (b - e) := by
  simpa using @HahnSeries.coeff_single_mul_add ℤ (LaurentPolynomial ℤ) _ _ _ _ c f (b - e) e
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

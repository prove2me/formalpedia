-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.isUnit_C_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:13:48.429206+00:00
-- url     : https://prove2.me/submissions/b31ac485-8cb5-401c-8a22-886fc35a2035

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℤ) : IsUnit (PowerSeries.C (LaurentPolynomial.T k) : R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C]
  exact LaurentPolynomial.isUnit_T k
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

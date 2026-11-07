-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.laurentPoly_T3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:40.968933+00:00
-- url     : https://prove2.me/submissions/9a0e0c5e-0e02-4850-ba3c-056e033360ef

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution :
    @T3Space (LaurentPolynomial ℤ) ((⊥ : UniformSpace (LaurentPolynomial ℤ)).toTopologicalSpace) :=
  { toT0Space := T4Space.instT35Space.toT0Space,
    toRegularSpace := CompletelyRegularSpace.instRegularSpace }
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

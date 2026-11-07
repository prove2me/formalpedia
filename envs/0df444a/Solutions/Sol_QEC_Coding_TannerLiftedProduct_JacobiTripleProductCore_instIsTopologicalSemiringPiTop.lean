-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.instIsTopologicalSemiringPiTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:08:03.803708+00:00
-- url     : https://prove2.me/submissions/ff1b46eb-f0ee-4ccf-aee6-489c950a8d4d

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : @IsTopologicalSemiring R piTop _ :=
  WithPiTopology.instIsTopologicalSemiring (LaurentPolynomial ℤ)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

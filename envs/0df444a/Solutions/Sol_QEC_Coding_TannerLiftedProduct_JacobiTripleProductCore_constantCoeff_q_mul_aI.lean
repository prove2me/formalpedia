-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.constantCoeff_q_mul_aI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:13:54.170147+00:00
-- url     : https://prove2.me/submissions/ee2921d7-b4fc-4a93-8f83-43c413669259

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : (q * aI : R).constantCoeff = 0 := by
  rw [map_mul, show (q : R).constantCoeff = 0 from PowerSeries.constantCoeff_X, zero_mul]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

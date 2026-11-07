-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.constantCoeff_P_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:35.084964+00:00
-- url     : https://prove2.me/submissions/35ed24d0-d625-4ed7-b487-4faad110cc86

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) :
    PowerSeries.constantCoeff (P k) = 1 :=
  by simp [P, qPoch, map_prod, map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

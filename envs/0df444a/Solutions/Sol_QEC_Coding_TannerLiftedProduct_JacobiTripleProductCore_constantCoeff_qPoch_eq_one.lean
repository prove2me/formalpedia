-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.constantCoeff_qPoch_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:08:44.100203+00:00
-- url     : https://prove2.me/submissions/4adba59d-d740-495a-8ba6-141341d4d0c8

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) :
    PowerSeries.constantCoeff (qPoch (q ^ 2) (q ^ 2) k : R) = 1 := by
  simp [qPoch, map_prod, map_sub, map_one, map_mul, map_pow, PowerSeries.constantCoeff_X]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

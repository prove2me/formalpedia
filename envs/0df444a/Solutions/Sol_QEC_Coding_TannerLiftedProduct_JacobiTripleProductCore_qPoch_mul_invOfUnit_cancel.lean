-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_mul_invOfUnit_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:10:20.171758+00:00
-- url     : https://prove2.me/submissions/057e5fc6-b3df-4196-a895-59e0312198b1

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_qPoch_eq_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) :
    qPoch (q ^ 2) (q ^ 2) k * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by simp [constantCoeff_qPoch_eq_one])
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

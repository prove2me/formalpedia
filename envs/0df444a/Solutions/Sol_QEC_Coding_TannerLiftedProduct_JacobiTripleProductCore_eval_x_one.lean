-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:50.34123+00:00
-- url     : https://prove2.me/submissions/2f8e2eb5-1075-4da3-96c0-8d1a8ed7bd37

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (_hx : x.constantCoeff = 0) :
    eval_x_fun x 1 = 1 := by
  show letI := piTop; ∑' n, (1 : S).coeff n * x ^ n = 1
  letI := piTop
  rw [tsum_eq_single 0 (fun n hn => by rw [PowerSeries.coeff_one, if_neg hn, zero_mul])]
  simp [PowerSeries.coeff_one]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

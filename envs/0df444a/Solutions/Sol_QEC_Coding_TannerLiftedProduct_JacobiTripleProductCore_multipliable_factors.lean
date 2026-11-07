-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.multipliable_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:47:09.082594+00:00
-- url     : https://prove2.me/submissions/d1c8a831-e9dd-499e-8588-ac7565d9e794

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factors_multipliable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    Multipliable (fun n ↦ 1 - q ^ 2 * (q ^ 2) ^ n) := by
  letI := piTop
  exact (factors_multipliable (-q) |>.congr (fun n => by simp [neg_neg]; ring))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

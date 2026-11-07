-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_neg_factor_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:32.22243+00:00
-- url     : https://prove2.me/submissions/1cb1f347-b44e-467d-8516-cdccc4cc05aa

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_lower_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_enat_add_two_mul_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) : letI := piTop;
    Filter.Tendsto (fun i => ((-x * q) * (q ^ 2) ^ i).order) Filter.atTop (nhds ⊤) :=
  tendsto_nhds_top_mono' (enat_add_two_mul_tendsto_top (-x * q).order)
    (fun i => order_lower_bound x i)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

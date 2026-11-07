-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_eval_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:40.467205+00:00
-- url     : https://prove2.me/submissions/7780e48e-f2fe-4b82-ac2c-6c3f001707ff

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {x : R} (hx : x.constantCoeff = 0) (p : S) :
    letI := piTop; Summable (fun n => p.coeff n * x ^ n) :=
  PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (order_tendsto_top hx p)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

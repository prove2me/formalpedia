-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.inner_sum_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:38:10.918798+00:00
-- url     : https://prove2.me/submissions/f1021dc4-3c06-467f-97df-000fb4aef48e

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_F_neg_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) : letI := piTop;
    Summable (fun ℓ : ℕ => F (-(↑j + 1), ℓ)) :=
  PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (order_F_neg_tendsto_top j)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

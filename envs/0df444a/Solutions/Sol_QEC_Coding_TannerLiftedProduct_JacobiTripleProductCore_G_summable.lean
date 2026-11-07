-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.G_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:16:18.345195+00:00
-- url     : https://prove2.me/submissions/afd84e86-fb24-49b2-a1cc-212178986129

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_natAbs_sq_add_tendsto_top
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_G_term_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) : letI := piTop;
    Summable (fun ℓ : ℕ =>
      (-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) := by
  letI := piTop
  exact PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (tendsto_nhds_top_mono' (natAbs_sq_add_tendsto_top j) (order_G_term_ge j))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

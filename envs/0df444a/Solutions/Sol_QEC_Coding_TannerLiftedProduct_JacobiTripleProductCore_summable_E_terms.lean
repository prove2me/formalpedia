-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_E_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:29:26.955502+00:00
-- url     : https://prove2.me/submissions/40849d0f-74e6-43d0-857e-f0c5951cac76

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tendsto_natCast_enat_atTop
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_E_term_ge_1

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    Summable (fun ℓ : ℕ => (-(q * aI)) ^ ℓ *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) :=
  PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top _
    (tendsto_nhds_top_mono' tendsto_natCast_enat_atTop order_E_term_ge_1)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

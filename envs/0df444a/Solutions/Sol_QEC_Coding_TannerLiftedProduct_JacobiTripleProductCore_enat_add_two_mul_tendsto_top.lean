-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.enat_add_two_mul_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:20:11.928644+00:00
-- url     : https://prove2.me/submissions/5b513b2e-6cd4-49e7-9f25-0f1c3bb8d28f

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_enat_two_mul_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (c : ℕ∞) :
    Filter.Tendsto (fun i : ℕ => c + 2 * (i : ℕ∞)) Filter.atTop (nhds ⊤) :=
  tendsto_nhds_top_mono' enat_two_mul_tendsto_top
    (fun _ => le_add_of_nonneg_left zero_le)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

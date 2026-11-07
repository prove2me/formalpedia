-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_neg_q_aI_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:36.716193+00:00
-- url     : https://prove2.me/submissions/d2d70fdf-f729-45d2-b867-e96c46a0ee41

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_lower_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_enat_add_two_mul_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution :
    Filter.Tendsto (fun n => ((-q * aI) * (q ^ 2) ^ n).order) Filter.atTop (nhds ⊤) := by
  simp_rw [show (-q * aI : R) = -aI * q by ring]
  exact tendsto_nhds_top_mono'
    (enat_add_two_mul_tendsto_top ((-aI * q).order)) (fun i => order_lower_bound aI i)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

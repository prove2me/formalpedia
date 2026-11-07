-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.order_F_neg_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:52.907259+00:00
-- url     : https://prove2.me/submissions/238b8089-06eb-4b2f-b914-4325b4c41bc2

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_F_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_natAbs_sq_add_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) :
    Filter.Tendsto (fun ℓ : ℕ => (F (-(↑j + 1), ℓ)).order)
      Filter.atTop (nhds ⊤) :=
  tendsto_nhds_top_mono' (natAbs_sq_add_tendsto_top j) fun ℓ =>
    by dsimp only; exact_mod_cast order_F_ge (-(↑j + 1)) ℓ
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

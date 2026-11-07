-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factors_multipliable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:24:29.995599+00:00
-- url     : https://prove2.me/submissions/e1f864b8-9f7f-4996-a92b-be20082667b2

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_neg_factor_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) : letI := piTop;
    Multipliable (fun i => 1 - (-x * q) * (q ^ 2) ^ i : ℕ → R) := by
  letI := piTop
  rw [show (fun i => 1 - (-x * q) * (q ^ 2) ^ i : ℕ → R) =
      (fun i => 1 + (-((-x * q) * (q ^ 2) ^ i))) from funext fun i => by ring_nf]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  simp_rw [PowerSeries.order_neg]
  exact order_neg_factor_tendsto_top x
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.multipliable_P3_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:53:41.044514+00:00
-- url     : https://prove2.me/submissions/6632ef26-de4d-4f4a-b0c0-99e0daeb5107

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_neg_q_aI_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    Multipliable (fun n : ℕ => 1 - (-q * aI) * (q ^ 2) ^ n : ℕ → R) := by
  letI := piTop
  have key : Filter.Tendsto (fun n => (-((-q * aI) * (q ^ 2) ^ n)).order) Filter.atTop (nhds ⊤) := by
    simp only [PowerSeries.order_neg]
    exact order_neg_q_aI_tendsto_top
  simpa only [sub_eq_add_neg, mul_assoc] using
    PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
      (R := LaurentPolynomial ℤ) key
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

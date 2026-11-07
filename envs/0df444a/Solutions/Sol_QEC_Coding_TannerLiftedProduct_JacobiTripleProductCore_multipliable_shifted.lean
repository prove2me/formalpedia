-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.multipliable_shifted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:55.936505+00:00
-- url     : https://prove2.me/submissions/aafc7aca-3135-46ef-8fdf-7c6557416adf

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_shifted_tendsto_top

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) : letI := piTop;
    Multipliable (fun n ↦ 1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n) := by
  letI := piTop
  have key : Filter.Tendsto
      (fun n ↦ (-(q ^ 2 * (q ^ 2) ^ k * (q ^ 2) ^ n)).order) Filter.atTop (nhds ⊤) := by
    simp only [PowerSeries.order_neg]
    exact order_shifted_tendsto_top k
  simpa only [sub_eq_add_neg, mul_assoc] using
    PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
      (R := LaurentPolynomial ℤ) key
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

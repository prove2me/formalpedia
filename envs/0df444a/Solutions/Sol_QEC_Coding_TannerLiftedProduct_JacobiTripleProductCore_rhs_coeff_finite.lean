-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.rhs_coeff_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:44.128902+00:00
-- url     : https://prove2.me/submissions/f318d5a2-f629-40d2-8fab-362b016b075b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_order_product_ge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_series_summable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m =
    ∑ k ∈ Finset.range (m + 1),
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1 : R).coeff m := by
  letI := piTop
  rw [(series_summable x).map_tsum (PowerSeries.coeff m)
    (PowerSeries.WithPiTopology.continuous_coeff _ m)]
  exact tsum_eq_sum fun k hk => by
    simp only [Finset.mem_range, not_lt] at hk
    exact PowerSeries.coeff_of_lt_order _
      (lt_of_lt_of_le (by exact_mod_cast show m < k ^ 2 by nlinarith) (order_product_ge x k))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

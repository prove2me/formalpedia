-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_jacobi_odd_plus_logDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:48:57.497356+00:00
-- url     : https://prove2.me/submissions/758627e1-6e65-480c-a68e-4d96d44ba38a

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_order_jacobiPlusLogDerivative_ge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Summable (fun n : ℕ => jacobiPlusLogDerivative (2 * n + 1)) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top ℚ
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩
  refine lt_of_lt_of_le ?_ (order_jacobiPlusLogDerivative_ge (2 * n + 1))
  norm_cast
  omega
end QEC.Coding.TannerLiftedProduct

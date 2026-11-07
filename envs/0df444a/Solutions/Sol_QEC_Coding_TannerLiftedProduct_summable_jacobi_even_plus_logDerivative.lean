-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_jacobi_even_plus_logDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:41.073198+00:00
-- url     : https://prove2.me/submissions/0f168aa9-66d6-48ad-be3a-df558ae62c8b

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
    Summable (fun n : ℕ => jacobiPlusLogDerivative (2 * (n + 1))) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top ℚ
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩
  refine lt_of_lt_of_le ?_ (order_jacobiPlusLogDerivative_ge (2 * (n + 1)))
  norm_cast
  omega
end QEC.Coding.TannerLiftedProduct

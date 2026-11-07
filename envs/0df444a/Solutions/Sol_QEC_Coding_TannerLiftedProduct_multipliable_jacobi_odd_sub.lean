-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.multipliable_jacobi_odd_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:51:09.556823+00:00
-- url     : https://prove2.me/submissions/d95f2156-0fe8-4638-9bf6-518d632b5ec8

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


section
namespace QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
private theorem tendsto_order_X_pow_two_mul_add_one :
    Filter.Tendsto
      (fun n : ℕ => ((PowerSeries.X : ℚ⟦X⟧) ^ (2 * n + 1)).order)
      Filter.atTop (nhds ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun k =>
    Filter.eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
  rw [PowerSeries.order_X_pow]
  norm_cast
  omega
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Multipliable (fun n : ℕ =>
      (1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * n + 1)) := by
  simpa only [sub_eq_add_neg] using
    PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top ℚ
      (f := fun n : ℕ => -((PowerSeries.X : ℚ⟦X⟧) ^ (2 * n + 1))) <| by
        simpa only [PowerSeries.order_neg] using tendsto_order_X_pow_two_mul_add_one
end QEC.Coding.TannerLiftedProduct

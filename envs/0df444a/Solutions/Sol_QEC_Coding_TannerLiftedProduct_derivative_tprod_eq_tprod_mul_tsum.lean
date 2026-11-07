-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.derivative_tprod_eq_tprod_mul_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:14.008284+00:00
-- url     : https://prove2.me/submissions/4eed35a7-96ed-40fb-8c1e-86775e21bf77

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_continuous_powerSeries_derivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_finset_prod_eq_prod_mul_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {I : Type*} (f l : I → ℚ⟦X⟧)
    (hf : Multipliable f) (hl : Summable l)
    (hlog : ∀ i, f i * l i = PowerSeries.derivative ℚ (f i)) :
    PowerSeries.derivative ℚ (∏' i, f i) =
      (∏' i, f i) * ∑' i, l i := by
  classical
  have hprod : Filter.Tendsto
      (fun s : Finset I => ∏ i ∈ s, f i) Filter.atTop
      (nhds (∏' i, f i)) := hf.hasProd
  have hsum : Filter.Tendsto
      (fun s : Finset I => ∑ i ∈ s, l i) Filter.atTop
      (nhds (∑' i, l i)) := hl.hasSum
  have hderiv : Filter.Tendsto
      (fun s : Finset I => PowerSeries.derivative ℚ (∏ i ∈ s, f i))
      Filter.atTop (nhds (PowerSeries.derivative ℚ (∏' i, f i))) :=
    (show Filter.Tendsto (PowerSeries.derivative ℚ)
        (nhds (∏' i, f i))
        (nhds (PowerSeries.derivative ℚ (∏' i, f i))) from
      continuous_powerSeries_derivative.continuousAt).comp hprod
  have hmul : Filter.Tendsto
      (fun s : Finset I => (∏ i ∈ s, f i) * ∑ i ∈ s, l i)
      Filter.atTop (nhds ((∏' i, f i) * ∑' i, l i)) :=
    hprod.mul hsum
  rw [Filter.tendsto_congr' <| Filter.Eventually.of_forall fun s =>
    derivative_finset_prod_eq_prod_mul_sum f l hlog s] at hderiv
  exact tendsto_nhds_unique hderiv hmul
end QEC.Coding.TannerLiftedProduct

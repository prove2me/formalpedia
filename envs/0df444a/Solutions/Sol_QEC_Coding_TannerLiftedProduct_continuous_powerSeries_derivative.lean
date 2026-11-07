-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.continuous_powerSeries_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:51:11.971281+00:00
-- url     : https://prove2.me/submissions/c0901077-88dd-42f4-9d91-6815c6714207

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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Continuous (PowerSeries.derivative ℚ : ℚ⟦X⟧ → ℚ⟦X⟧) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  simp only [PowerSeries.coeff_derivative]
  change ContinuousAt
    ((fun g : ℚ⟦X⟧ => PowerSeries.coeff (n + 1) g) *
      (fun _ => (n + 1 : ℚ))) f
  exact ((PowerSeries.WithPiTopology.continuous_coeff ℚ (n + 1)).mul
    continuous_const).continuousAt
end QEC.Coding.TannerLiftedProduct

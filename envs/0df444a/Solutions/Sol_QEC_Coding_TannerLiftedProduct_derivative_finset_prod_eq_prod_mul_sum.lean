-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.derivative_finset_prod_eq_prod_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:55:08.131614+00:00
-- url     : https://prove2.me/submissions/141a2926-9eb7-494b-b992-a86cfa18f7c4

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
theorem _root_.solution
    {I : Type*} [DecidableEq I] (f l : I → ℚ⟦X⟧)
    (hlog : ∀ i, f i * l i = PowerSeries.derivative ℚ (f i))
    (s : Finset I) :
    PowerSeries.derivative ℚ (∏ i ∈ s, f i) =
      (∏ i ∈ s, f i) * ∑ i ∈ s, l i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [(PowerSeries.derivative ℚ).leibniz, ih, ← hlog a]
      simp only [smul_eq_mul]
      ring
end QEC.Coding.TannerLiftedProduct

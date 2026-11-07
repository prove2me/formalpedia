-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiOddMinusSquareProduct_mul_evenMinusSquareProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:59:02.08326+00:00
-- url     : https://prove2.me/submissions/185e1229-10f8-4a22-9a28-3cae4ab23a02

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_sub
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_odd_sub
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiOddMinusSquareProduct *
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) =
      jacobiEulerSquareProduct := by
  rw [jacobiOddMinusSquareProduct, jacobiEulerSquareProduct]
  let f : ℕ → ℚ⟦X⟧ := fun n =>
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 2
  have he : (fun k => f (2 * k)) = fun n =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * n + 1)) ^ 2 := by
    funext n
    rfl
  have ho : (fun k => f (2 * k + 1)) = fun n =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2 := by
    funext n
    simp only [f]
    congr 3
  have hEven : Multipliable (fun k => f (2 * k)) := by
    rw [he]
    exact multipliable_jacobi_odd_sub.pow 2
  have hOdd : Multipliable (fun k => f (2 * k + 1)) := by
    rw [ho]
    exact multipliable_jacobi_even_sub.pow 2
  have h := tprod_even_mul_odd (f := f) hEven hOdd
  rw [he, ho] at h
  exact h
end QEC.Coding.TannerLiftedProduct

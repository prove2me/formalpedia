-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.multipliable_jacobiAllPlusSquareFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:59:03.730996+00:00
-- url     : https://prove2.me/submissions/563c0e32-9547-4306-bcc1-038f69b6b406

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_odd_add
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
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (n + 1)) ^ 2) := by
  let f : ℕ → ℚ⟦X⟧ := fun n =>
    ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (n + 1)) ^ 2
  change Multipliable f
  apply Multipliable.even_mul_odd (f := f)
  · simpa only [f] using multipliable_jacobi_odd_add.pow 2
  · convert multipliable_jacobi_even_add.pow 2 using 1
    funext n
    simp only [f]
    congr 3
end QEC.Coding.TannerLiftedProduct

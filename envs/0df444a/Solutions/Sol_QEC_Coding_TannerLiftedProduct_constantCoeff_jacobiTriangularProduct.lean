-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:58:59.18589+00:00
-- url     : https://prove2.me/submissions/2aca6cfd-d799-4f0b-a379-67d5e6f758a0

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_triangular_factor
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
    PowerSeries.constantCoeff jacobiTriangularProduct = 1 := by
  rw [jacobiTriangularProduct]
  calc
    PowerSeries.constantCoeff
        (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
            (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) =
        ∏' n : ℕ,
          PowerSeries.constantCoeff
            (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
              (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2) :=
      multipliable_jacobi_triangular_factor.map_tprod
        (PowerSeries.constantCoeff (R := ℚ))
        (PowerSeries.WithPiTopology.continuous_constantCoeff ℚ)
    _ = 1 := by simp
end QEC.Coding.TannerLiftedProduct

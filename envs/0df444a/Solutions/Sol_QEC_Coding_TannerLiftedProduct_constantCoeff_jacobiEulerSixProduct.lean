-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:55.366125+00:00
-- url     : https://prove2.me/submissions/b25d3cd5-acbd-4493-9867-0c35179ead3a

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobiEulerSixFactor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.constantCoeff jacobiEulerSixProduct = 1 := by
  rw [jacobiEulerSixProduct]
  calc
    PowerSeries.constantCoeff
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 6) =
      ∏' n : ℕ, PowerSeries.constantCoeff
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 6) :=
      multipliable_jacobiEulerSixFactor.map_tprod
        (PowerSeries.constantCoeff (R := ℚ))
        (PowerSeries.WithPiTopology.continuous_constantCoeff ℚ)
    _ = 1 := by simp
end QEC.Coding.TannerLiftedProduct

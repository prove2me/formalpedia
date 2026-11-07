-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.derivative_one_sub_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:11.29348+00:00
-- url     : https://prove2.me/submissions/1dda02b5-bd97-44d1-99df-c2800d4f8647

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
theorem _root_.solution (d : ℕ) :
    PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) =
      -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1)) := by
  rw [map_sub, PowerSeries.derivative_one, PowerSeries.derivative_pow,
    PowerSeries.derivative_X]
  simp
end QEC.Coding.TannerLiftedProduct

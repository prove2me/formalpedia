-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.derivative_one_add_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:12.805121+00:00
-- url     : https://prove2.me/submissions/7b920726-a257-4e88-b5af-46713fe62001

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
        ((1 : ℚ⟦X⟧) + PowerSeries.X ^ d) =
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) := by
  rw [map_add, PowerSeries.derivative_one, PowerSeries.derivative_pow,
    PowerSeries.derivative_X]
  simp
end QEC.Coding.TannerLiftedProduct

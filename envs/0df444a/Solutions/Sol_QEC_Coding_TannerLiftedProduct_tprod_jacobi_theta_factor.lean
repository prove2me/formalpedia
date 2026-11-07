-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tprod_jacobi_theta_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:37.894996+00:00
-- url     : https://prove2.me/submissions/d4fce4cc-365f-4f43-a399-a1e0ac3e4763

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_sub
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_odd_add
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
    (∏' n : ℕ,
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) =
      (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) *
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1))) ^ 2 := by
  calc
    _ = (∏' n : ℕ, ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) *
        (∏' n : ℕ, ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2) :=
      by simpa using
        multipliable_jacobi_even_sub.tprod_mul (multipliable_jacobi_odd_add.pow 2)
    _ = _ := congrArg
      (fun z => (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1)))) * z)
      (multipliable_jacobi_odd_add.tprod_pow 2)
end QEC.Coding.TannerLiftedProduct

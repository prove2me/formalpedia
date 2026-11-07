-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_mul_jacobiTriangularProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:02:03.224743+00:00
-- url     : https://prove2.me/submissions/cc8f1f77-ed4e-4fa7-a1d4-f6f73a9853ae

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_odd_add
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_theta_factor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobiEvenMinusSquareFactor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_tprod_jacobi_odd_even_add_square
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_triangular_factor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiThetaProduct * jacobiTriangularProduct =
      jacobiEvenMinusSquareProduct * jacobiAllPlusSquareProduct := by
  rw [jacobiThetaProduct, jacobiTriangularProduct,
    jacobiEvenMinusSquareProduct]
  rw [← multipliable_jacobi_theta_factor.tprod_mul
    multipliable_jacobi_triangular_factor]
  calc
    (∏' n : ℕ,
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
          (1 + PowerSeries.X ^ (2 * n + 1)) ^ 2) *
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
          (1 + PowerSeries.X ^ (2 * (n + 1))) ^ 2)) =
      ∏' n : ℕ,
        (((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2 *
          (((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2 *
            ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2)) :=
      tprod_congr fun n => by ring
    _ = (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) *
        (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2 *
            ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2) :=
      multipliable_jacobiEvenMinusSquareFactor.tprod_mul
        ((multipliable_jacobi_odd_add.pow 2).mul
          (multipliable_jacobi_even_add.pow 2))
    _ = (∏' n : ℕ,
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) *
        ((∏' n : ℕ,
            ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * n + 1)) ^ 2) *
          (∏' n : ℕ,
            ((1 : ℚ⟦X⟧) + PowerSeries.X ^ (2 * (n + 1))) ^ 2)) := by
      rw [(multipliable_jacobi_odd_add.pow 2).tprod_mul
        (multipliable_jacobi_even_add.pow 2)]
    _ = _ := by rw [tprod_jacobi_odd_even_add_square]
end QEC.Coding.TannerLiftedProduct

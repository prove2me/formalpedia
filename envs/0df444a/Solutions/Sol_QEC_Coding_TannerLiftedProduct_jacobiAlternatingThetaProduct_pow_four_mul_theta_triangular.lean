-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_pow_four_mul_theta_triangular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:04:17.115407+00:00
-- url     : https://prove2.me/submissions/65e43964-a6e7-4a43-b86d-dfb4d05782d0

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEulerSixProduct_eq_squareProduct_cubed
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_sq_mul_allPlusSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaProduct_mul_jacobiTriangularProduct_eq_eulerSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiAlternatingThetaProduct ^ 4 *
        (jacobiThetaProduct * jacobiTriangularProduct) =
      jacobiEulerSixProduct := by
  rw [jacobiThetaProduct_mul_jacobiTriangularProduct_eq_eulerSquare,
    jacobiEulerSixProduct_eq_squareProduct_cubed]
  calc
    jacobiAlternatingThetaProduct ^ 4 *
        (jacobiEulerSquareProduct * jacobiAllPlusSquareProduct ^ 2) =
      jacobiEulerSquareProduct *
        (jacobiAlternatingThetaProduct ^ 2 *
          jacobiAllPlusSquareProduct) ^ 2 := by ring
    _ = jacobiEulerSquareProduct * jacobiEulerSquareProduct ^ 2 := by
      rw [jacobiAlternatingThetaProduct_sq_mul_allPlusSquare]
    _ = jacobiEulerSquareProduct ^ 3 := by ring
end QEC.Coding.TannerLiftedProduct

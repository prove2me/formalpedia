-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiThetaProduct_mul_jacobiTriangularProduct_eq_eulerSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:03:12.094998+00:00
-- url     : https://prove2.me/submissions/28b1cf4f-2eef-436c-8433-f531263bf3b3

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaProduct_mul_jacobiTriangularProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiThetaProduct * jacobiTriangularProduct =
      jacobiEulerSquareProduct * jacobiAllPlusSquareProduct ^ 2 := by
  rw [jacobiThetaProduct_mul_jacobiTriangularProduct,
    jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare]
  ring
end QEC.Coding.TannerLiftedProduct

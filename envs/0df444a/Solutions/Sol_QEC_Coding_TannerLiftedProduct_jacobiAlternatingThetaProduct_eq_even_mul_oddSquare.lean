-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_eq_even_mul_oddSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:30.852535+00:00
-- url     : https://prove2.me/submissions/49d9cfd6-f97e-46a3-a431-f9f084954015

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_sub
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobiOddMinusSquareFactor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiAlternatingThetaProduct =
      jacobiEvenMinusProduct * jacobiOddMinusSquareProduct := by
  rw [jacobiAlternatingThetaProduct, jacobiEvenMinusProduct,
    jacobiOddMinusSquareProduct]
  exact multipliable_jacobi_even_sub.tprod_mul
    multipliable_jacobiOddMinusSquareFactor
end QEC.Coding.TannerLiftedProduct

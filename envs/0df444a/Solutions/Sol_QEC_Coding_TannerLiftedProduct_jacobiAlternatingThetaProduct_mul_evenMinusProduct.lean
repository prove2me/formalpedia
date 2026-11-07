-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_mul_evenMinusProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:02:01.543199+00:00
-- url     : https://prove2.me/submissions/37b3f345-604e-4b4c-ab64-54c03425e226

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_eq_even_mul_oddSquare
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiOddMinusSquareProduct_mul_evenMinusSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiAlternatingThetaProduct * jacobiEvenMinusProduct =
      jacobiEulerSquareProduct := by
  rw [jacobiAlternatingThetaProduct_eq_even_mul_oddSquare]
  calc
    (jacobiEvenMinusProduct * jacobiOddMinusSquareProduct) *
        jacobiEvenMinusProduct =
      jacobiOddMinusSquareProduct * jacobiEvenMinusProduct ^ 2 := by ring
    _ = jacobiOddMinusSquareProduct * jacobiEvenMinusSquareProduct := by
      rw [jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq]
    _ = jacobiEulerSquareProduct :=
      jacobiOddMinusSquareProduct_mul_evenMinusSquareProduct
end QEC.Coding.TannerLiftedProduct

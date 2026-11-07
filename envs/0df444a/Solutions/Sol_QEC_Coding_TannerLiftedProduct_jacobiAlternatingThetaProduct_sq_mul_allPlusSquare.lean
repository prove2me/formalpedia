-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiAlternatingThetaProduct_sq_mul_allPlusSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:03:10.598679+00:00
-- url     : https://prove2.me/submissions/f588940a-eab2-428b-94fb-7adf7797714b

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_isUnit_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiAlternatingThetaProduct_mul_evenMinusProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiAlternatingThetaProduct ^ 2 * jacobiAllPlusSquareProduct =
      jacobiEulerSquareProduct := by
  apply isUnit_jacobiEulerSquareProduct.mul_left_cancel
  calc
    jacobiEulerSquareProduct *
        (jacobiAlternatingThetaProduct ^ 2 *
          jacobiAllPlusSquareProduct) =
      jacobiAlternatingThetaProduct ^ 2 *
        (jacobiEulerSquareProduct * jacobiAllPlusSquareProduct) := by ring
    _ = jacobiAlternatingThetaProduct ^ 2 *
        jacobiEvenMinusSquareProduct := by
      rw [jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare]
    _ = (jacobiAlternatingThetaProduct * jacobiEvenMinusProduct) ^ 2 := by
      rw [jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq]
      ring
    _ = jacobiEulerSquareProduct ^ 2 := by
      rw [jacobiAlternatingThetaProduct_mul_evenMinusProduct]
    _ = jacobiEulerSquareProduct * jacobiEulerSquareProduct := by ring
end QEC.Coding.TannerLiftedProduct

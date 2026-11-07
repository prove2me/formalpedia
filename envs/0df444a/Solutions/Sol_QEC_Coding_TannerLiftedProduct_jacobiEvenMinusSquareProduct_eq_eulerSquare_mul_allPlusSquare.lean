-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiEvenMinusSquareProduct_eq_eulerSquare_mul_allPlusSquare
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:00:54.784365+00:00
-- url     : https://prove2.me/submissions/bdebfeab-2873-4ec5-9f30-b1ba00a60c5f

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobiEulerSquareFactor
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobiAllPlusSquareFactor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiEvenMinusSquareProduct =
      jacobiEulerSquareProduct * jacobiAllPlusSquareProduct := by
  rw [jacobiEvenMinusSquareProduct, jacobiEulerSquareProduct,
    jacobiAllPlusSquareProduct,
    ← multipliable_jacobiEulerSquareFactor.tprod_mul
      multipliable_jacobiAllPlusSquareFactor]
  apply tprod_congr
  intro n
  rw [show 2 * (n + 1) = (n + 1) * 2 by omega, pow_mul]
  ring
end QEC.Coding.TannerLiftedProduct

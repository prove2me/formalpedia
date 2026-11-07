-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiEulerSixProduct_eq_squareProduct_cubed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:06.422519+00:00
-- url     : https://prove2.me/submissions/f14eca0c-05f1-4cd1-9b20-c47ef280c863

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobiEulerSquareFactor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiEulerSixProduct = jacobiEulerSquareProduct ^ 3 := by
  rw [jacobiEulerSixProduct, jacobiEulerSquareProduct,
    ← multipliable_jacobiEulerSquareFactor.tprod_pow]
  apply tprod_congr
  intro n
  ring
end QEC.Coding.TannerLiftedProduct

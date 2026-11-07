-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiEvenMinusSquareProduct_eq_evenMinusProduct_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:52:01.54821+00:00
-- url     : https://prove2.me/submissions/aa119a4c-61d9-405d-9d20-cb5c3eca5fe3

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_sub

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiEvenMinusSquareProduct = jacobiEvenMinusProduct ^ 2 := by
  rw [jacobiEvenMinusSquareProduct, jacobiEvenMinusProduct]
  exact multipliable_jacobi_even_sub.tprod_pow 2
end QEC.Coding.TannerLiftedProduct

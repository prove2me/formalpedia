-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.multipliable_jacobiEvenMinusSquareFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:19.134518+00:00
-- url     : https://prove2.me/submissions/28640de5-a3b4-4cce-b506-6c25e25d4f43

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
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) ^ 2) :=
  multipliable_jacobi_even_sub.pow 2
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.multipliable_jacobiAlternatingThetaFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:58:11.680697+00:00
-- url     : https://prove2.me/submissions/f60866ba-91d7-4434-9b83-c9eab0b75555

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_even_sub
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_odd_sub

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (2 * (n + 1))) *
        (1 - PowerSeries.X ^ (2 * n + 1)) ^ 2) :=
  multipliable_jacobi_even_sub.mul (multipliable_jacobi_odd_sub.pow 2)
end QEC.Coding.TannerLiftedProduct

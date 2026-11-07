-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.multipliable_jacobiEulerSquareFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:51:10.714685+00:00
-- url     : https://prove2.me/submissions/6c92a6ba-0b53-49a4-80ee-c6512a59113f

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Multipliable (fun n : ℕ =>
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 2) :=
  (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℚ).pow 2
end QEC.Coding.TannerLiftedProduct

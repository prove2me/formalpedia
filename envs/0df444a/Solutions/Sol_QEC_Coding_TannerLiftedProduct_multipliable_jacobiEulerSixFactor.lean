-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.multipliable_jacobiEulerSixFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:02.331626+00:00
-- url     : https://prove2.me/submissions/eb389c2b-f23c-4f41-a44b-e384421ce7c2

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
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1)) ^ 6) :=
  (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℚ).pow 6
end QEC.Coding.TannerLiftedProduct

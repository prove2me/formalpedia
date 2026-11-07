-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiEulerSixProduct_eq_tprod_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:58:09.334761+00:00
-- url     : https://prove2.me/submissions/a2e9e2c7-6b7d-4eed-bd43-cabe87628ae6

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
    jacobiEulerSixProduct =
      (∏' n : ℕ,
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ (n + 1))) ^ 6 := by
  rw [jacobiEulerSixProduct]
  exact (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℚ).tprod_pow 6
end QEC.Coding.TannerLiftedProduct

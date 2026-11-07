-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.derivative_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:03.642448+00:00
-- url     : https://prove2.me/submissions/f4a6c465-85ad-4f27-8ddc-53959f28cf8b

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_continuous_powerSeries_derivative

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution {I : Type*} (f : I → ℚ⟦X⟧) (hf : Summable f) :
    PowerSeries.derivative ℚ (∑' i, f i) =
      ∑' i, PowerSeries.derivative ℚ (f i) := by
  exact hf.map_tsum (PowerSeries.derivative ℚ) continuous_powerSeries_derivative
end QEC.Coding.TannerLiftedProduct

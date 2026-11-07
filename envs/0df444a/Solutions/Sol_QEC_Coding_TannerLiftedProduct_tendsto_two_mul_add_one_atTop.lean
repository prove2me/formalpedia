-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.tendsto_two_mul_add_one_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:36.506741+00:00
-- url     : https://prove2.me/submissions/aa2171d8-10b0-4b34-ad5f-ac4d4d756ab2

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
    Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with a ha
  omega
end QEC.Coding.TannerLiftedProduct

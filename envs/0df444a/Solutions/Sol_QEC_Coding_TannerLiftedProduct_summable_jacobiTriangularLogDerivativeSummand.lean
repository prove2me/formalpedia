-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_jacobiTriangularLogDerivativeSummand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:07.006651+00:00
-- url     : https://prove2.me/submissions/667cfbc0-fef9-416f-bab6-d042cd32cb5c

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobi_even_minus_logDerivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobi_even_plus_logDerivative

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Summable jacobiTriangularLogDerivativeSummand := by
  exact summable_jacobi_even_minus_logDerivative.add
    (Summable.mul_left 2 summable_jacobi_even_plus_logDerivative)
end QEC.Coding.TannerLiftedProduct

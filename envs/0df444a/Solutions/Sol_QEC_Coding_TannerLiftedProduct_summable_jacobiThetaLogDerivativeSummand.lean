-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.summable_jacobiThetaLogDerivativeSummand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:51:03.034096+00:00
-- url     : https://prove2.me/submissions/6d8c46c2-0ce1-4357-952e-26822101571a

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobi_even_minus_logDerivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobi_odd_plus_logDerivative

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Summable jacobiThetaLogDerivativeSummand := by
  exact summable_jacobi_even_minus_logDerivative.add
    (Summable.mul_left 2 summable_jacobi_odd_plus_logDerivative)
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.derivative_jacobiThetaProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:04.989209+00:00
-- url     : https://prove2.me/submissions/14c8a801-c9f1-4d85-92bb-67dbcdf8ba19

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobiThetaLogDerivativeSummand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_theta_factor_mul_logDerivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_tprod_eq_tprod_mul_tsum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_theta_factor


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.derivative ℚ jacobiThetaProduct =
      jacobiThetaProduct * jacobiThetaLogDerivative := by
  rw [jacobiThetaProduct, jacobiThetaLogDerivative]
  exact derivative_tprod_eq_tprod_mul_tsum _ _
    multipliable_jacobi_theta_factor
    summable_jacobiThetaLogDerivativeSummand
    jacobi_theta_factor_mul_logDerivative
end QEC.Coding.TannerLiftedProduct

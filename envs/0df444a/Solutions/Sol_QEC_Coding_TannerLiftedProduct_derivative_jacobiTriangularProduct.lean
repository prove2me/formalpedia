-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.derivative_jacobiTriangularProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:53:18.258008+00:00
-- url     : https://prove2.me/submissions/4181cbdc-5f8b-4c38-b322-695015050b0f

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobiTriangularLogDerivativeSummand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_triangular_factor_mul_logDerivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_tprod_eq_tprod_mul_tsum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_multipliable_jacobi_triangular_factor


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    PowerSeries.derivative ℚ jacobiTriangularProduct =
      jacobiTriangularProduct * jacobiTriangularLogDerivative := by
  rw [jacobiTriangularProduct, jacobiTriangularLogDerivative]
  exact derivative_tprod_eq_tprod_mul_tsum _ _
    multipliable_jacobi_triangular_factor
    summable_jacobiTriangularLogDerivativeSummand
    jacobi_triangular_factor_mul_logDerivative
end QEC.Coding.TannerLiftedProduct

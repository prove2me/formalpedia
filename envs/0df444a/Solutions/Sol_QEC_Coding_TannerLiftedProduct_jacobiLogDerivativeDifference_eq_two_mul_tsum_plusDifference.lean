-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiLogDerivativeDifference_eq_two_mul_tsum_plusDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:55:07.475354+00:00
-- url     : https://prove2.me/submissions/f4b89ccb-32be-4252-b915-dd40f078bac2

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobiThetaLogDerivativeSummand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobiTriangularLogDerivativeSummand
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobi_even_plus_logDerivative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_summable_jacobi_odd_plus_logDerivative

section
namespace QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
private theorem summable_jacobiPlusDifference :
    Summable (fun n : ℕ =>
      jacobiPlusLogDerivative (2 * (n + 1)) -
        jacobiPlusLogDerivative (2 * n + 1)) :=
  summable_jacobi_even_plus_logDerivative.sub
    summable_jacobi_odd_plus_logDerivative
end QEC.Coding.TannerLiftedProduct
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiLogDerivativeDifference =
      2 * ∑' n : ℕ,
        (jacobiPlusLogDerivative (2 * (n + 1)) -
          jacobiPlusLogDerivative (2 * n + 1)) := by
  rw [jacobiLogDerivativeDifference, jacobiTriangularLogDerivative,
    jacobiThetaLogDerivative]
  have hdiff := summable_jacobiTriangularLogDerivativeSummand.hasSum.sub
    summable_jacobiThetaLogDerivativeSummand.hasSum
  rw [← hdiff.tsum_eq]
  rw [← summable_jacobiPlusDifference.tsum_mul_left 2]
  apply tsum_congr
  intro n
  rw [jacobiTriangularLogDerivativeSummand,
    jacobiThetaLogDerivativeSummand]
  ring
end QEC.Coding.TannerLiftedProduct

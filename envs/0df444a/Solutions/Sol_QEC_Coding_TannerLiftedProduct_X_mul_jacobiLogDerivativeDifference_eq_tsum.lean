-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.X_mul_jacobiLogDerivativeDifference_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:57:03.643245+00:00
-- url     : https://prove2.me/submissions/653e9e7a-0913-423b-b015-b62371412e7c

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLogDerivativeDifference_eq_two_mul_tsum_plusDifference
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
    PowerSeries.X * jacobiLogDerivativeDifference =
      2 * ∑' n : ℕ,
        PowerSeries.X *
          (jacobiPlusLogDerivative (2 * (n + 1)) -
            jacobiPlusLogDerivative (2 * n + 1)) := by
  rw [jacobiLogDerivativeDifference_eq_two_mul_tsum_plusDifference]
  calc
    PowerSeries.X *
        (2 * ∑' n : ℕ,
          (jacobiPlusLogDerivative (2 * (n + 1)) -
            jacobiPlusLogDerivative (2 * n + 1))) =
      2 * (PowerSeries.X *
        ∑' n : ℕ,
          (jacobiPlusLogDerivative (2 * (n + 1)) -
            jacobiPlusLogDerivative (2 * n + 1))) := by ring
    _ = _ := by
      rw [← summable_jacobiPlusDifference.tsum_mul_left PowerSeries.X]
end QEC.Coding.TannerLiftedProduct

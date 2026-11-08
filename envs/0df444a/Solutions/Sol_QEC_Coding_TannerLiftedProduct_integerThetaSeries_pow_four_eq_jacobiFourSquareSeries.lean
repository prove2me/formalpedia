-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.integerThetaSeries_pow_four_eq_jacobiFourSquareSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:11:25.012615+00:00
-- url     : https://prove2.me/submissions/b3532dbb-a192-4811-8afa-43acf5409498

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductSpecialization
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiFourSquareIdentity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_rationalIntegerThetaSeries_pow_four_eq_jacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerThetaSeries_pow_four_eq_jacobi_of_rational


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    integerThetaSeries ^ 4 = jacobiFourSquareSeries :=
  integerThetaSeries_pow_four_eq_jacobi_of_rational
    rationalIntegerThetaSeries_pow_four_eq_jacobiLambertSeries
end QEC.Coding.TannerLiftedProduct

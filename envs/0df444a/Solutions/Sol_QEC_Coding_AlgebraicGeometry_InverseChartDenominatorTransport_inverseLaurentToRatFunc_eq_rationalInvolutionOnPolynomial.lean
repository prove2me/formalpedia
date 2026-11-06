-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.inverseLaurentToRatFunc_eq_rationalInvolutionOnPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:28:58.335563+00:00
-- url     : https://prove2.me/submissions/6e1d8077-b8a7-43db-b6f7-4a5143723307

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_rationalInvolution_X


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
theorem _root_.solution
    (k : Type*) [Field k] :
    inverseLaurentToRatFunc k = rationalInvolutionOnPolynomial k := by
  apply Polynomial.ringHom_ext
  · intro c
    simpa [inverseLaurentToRatFunc, rationalInvolutionOnPolynomial,
      directLaurentToRatFunc, inverseLaurentCoordinate, ratFuncXUnit]
      using ((InverseAffinePlace.rationalInvolution k).commutes c).symm
  · simpa [inverseLaurentToRatFunc, rationalInvolutionOnPolynomial,
      directLaurentToRatFunc, inverseLaurentCoordinate, ratFuncXUnit]
      using (InverseAffinePlace.rationalInvolution_X k).symm
end QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport

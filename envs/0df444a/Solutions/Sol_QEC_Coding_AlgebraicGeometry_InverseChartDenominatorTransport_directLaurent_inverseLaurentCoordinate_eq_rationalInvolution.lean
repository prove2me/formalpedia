-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport.directLaurent_inverseLaurentCoordinate_eq_rationalInvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:19.719465+00:00
-- url     : https://prove2.me/submissions/a13628d0-e0bd-4810-9a4d-6d52d9cba275

import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseChartDenominatorTransport_inverseLaurentToRatFunc_eq_rationalInvolutionOnPolynomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport
theorem _root_.solution
    (k : Type*) [Field k] (p : k[X]) :
    directLaurentToRatFunc k (inverseLaurentCoordinate k p) =
      InverseAffinePlace.rationalInvolution k (algebraMap k[X] (RatFunc k) p) := by
  change inverseLaurentToRatFunc k p = rationalInvolutionOnPolynomial k p
  rw [inverseLaurentToRatFunc_eq_rationalInvolutionOnPolynomial]
end QEC.Coding.AlgebraicGeometry.InverseChartDenominatorTransport

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurent_directCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:12.004862+00:00
-- url     : https://prove2.me/submissions/22100e7a-70de-4085-b86e-08a51b763f84

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_directCoordinate_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
theorem _root_.solution
    (k : Type*) [Field k] (p : Polynomial k) :
    InverseChartDenominatorTransport.directLaurentToRatFunc k
      (LaurentFiniteWindow.directCoordinate k p) =
      algebraMap (Polynomial k) (RatFunc k) p := by
  simp only [LaurentFiniteWindow.directCoordinate_apply,
    InverseChartDenominatorTransport.directLaurentToRatFunc,
    LaurentPolynomial.eval₂_toLaurent]
  rw [← Polynomial.aeval_def]
  exact RatFunc.aeval_X_left_eq_algebraMap p
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge

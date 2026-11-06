-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.directLaurentWindow_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:35:04.244907+00:00
-- url     : https://prove2.me/submissions/0246a98e-affb-465a-a60e-7e7024515f56

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_laurentWindow_finiteDimensional


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
theorem _root_.solution (k : Type*) [Field k]
    (lower upper : ℤ) :
    FiniteDimensional k (directLaurentWindow k lower upper) := by
  let := LaurentFiniteWindow.laurentWindow_finiteDimensional k lower upper
  exact LinearMap.finiteDimensional_range _
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge

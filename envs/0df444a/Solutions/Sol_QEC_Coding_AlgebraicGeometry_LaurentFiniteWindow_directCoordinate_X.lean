-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.directCoordinate_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:50.218252+00:00
-- url     : https://prove2.me/submissions/5a265454-cab5-4f57-9f10-a6238698af7c

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution :
    directCoordinate k Polynomial.X = LaurentPolynomial.T (R := k) 1 := by
  simp [directCoordinate]
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

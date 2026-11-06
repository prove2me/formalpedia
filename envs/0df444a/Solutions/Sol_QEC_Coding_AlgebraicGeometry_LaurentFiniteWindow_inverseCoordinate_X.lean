-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.inverseCoordinate_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:57.914224+00:00
-- url     : https://prove2.me/submissions/1cfc678e-7d91-4ef5-ba30-572a71aa8383

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution :
    inverseCoordinate k Polynomial.X = LaurentPolynomial.T (R := k) (-1) := by
  simp [inverseCoordinate]
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

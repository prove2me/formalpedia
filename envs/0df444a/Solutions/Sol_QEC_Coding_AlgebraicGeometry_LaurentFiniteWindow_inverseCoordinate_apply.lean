-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.inverseCoordinate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:04:21.645019+00:00
-- url     : https://prove2.me/submissions/69ac289f-15a1-41f0-ace0-7da528761a51

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (p : k[X]) :
    inverseCoordinate k p = LaurentPolynomial.invert p.toLaurent :=
  rfl
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

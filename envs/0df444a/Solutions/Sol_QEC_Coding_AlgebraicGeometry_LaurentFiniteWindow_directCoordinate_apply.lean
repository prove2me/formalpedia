-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.directCoordinate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:03:45.458125+00:00
-- url     : https://prove2.me/submissions/8c36110f-ff4f-44c9-99b7-8ed81e06a00d

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (p : k[X]) :
    directCoordinate k p = p.toLaurent :=
  rfl
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

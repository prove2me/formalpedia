-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurentWindow_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:09.206197+00:00
-- url     : https://prove2.me/submissions/9f1c3747-9059-47b6-9f69-25e5739c41d1

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_laurentWindow_eq_span

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (lower upper : ℤ) :
    FiniteDimensional k (laurentWindow k lower upper) := by
  rw [laurentWindow_eq_span]
  exact FiniteDimensional.span_of_finite k (Finset.finite_toSet _)
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.laurent_sum_C_mul_T_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:15.298019+00:00
-- url     : https://prove2.me/submissions/0aaf5220-011b-4e5c-90ff-4f3d14068417

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (f : LaurentPolynomial k) :
    f.coeff.support.sum (fun n : ℤ =>
      LaurentPolynomial.C (R := k) (f.coeff n) * LaurentPolynomial.T (R := k) n) = f := by
  simpa only [← LaurentPolynomial.single_eq_C_mul_T, Finsupp.sum] using
    AddMonoidAlgebra.sum_coeff_single f
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

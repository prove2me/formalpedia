-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow.direct_inverse_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:29:58.829789+00:00
-- url     : https://prove2.me/submissions/2006ec70-0365-4438-a5fd-30b1451fd42f

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_directCoordinate_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LaurentFiniteWindow_inverseCoordinate_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
open scoped Polynomial Pointwise
variable (k : Type*) [Field k]
namespace QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow
theorem _root_.solution (m n : ℕ) :
    directCoordinate k (Polynomial.X ^ m) * inverseCoordinate k (Polynomial.X ^ n) =
      LaurentPolynomial.T (R := k) ((m : ℤ) - n) := by
  calc
    directCoordinate k (Polynomial.X ^ m) * inverseCoordinate k (Polynomial.X ^ n) =
        LaurentPolynomial.T (R := k) (m : ℤ) * LaurentPolynomial.T (R := k) (-(n : ℤ)) := by
      simp only [directCoordinate_apply, inverseCoordinate_apply,
        Polynomial.toLaurent_X_pow, LaurentPolynomial.invert_T]
    _ = LaurentPolynomial.T (R := k) ((m : ℤ) + -(n : ℤ)) :=
      (LaurentPolynomial.T_add (R := k) (m : ℤ) (-(n : ℤ))).symm
    _ = LaurentPolynomial.T (R := k) ((m : ℤ) - n) := by
      rw [sub_eq_add_neg]
end QEC.Coding.AlgebraicGeometry.LaurentFiniteWindow

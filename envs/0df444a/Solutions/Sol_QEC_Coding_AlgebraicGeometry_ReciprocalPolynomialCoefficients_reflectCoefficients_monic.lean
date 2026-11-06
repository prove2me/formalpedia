-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_monic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:16.197288+00:00
-- url     : https://prove2.me/submissions/321991fe-ec74-4da9-843e-83483005bfe8

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_coeff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_degree

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
theorem _root_.solution (m r : ℕ) (Φ : Polynomial (Polynomial k))
    (hdegree : Φ.natDegree ≤ r)
    (htop : Φ.coeff r = Polynomial.X^m) :
    (reflectCoefficients m Φ).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one r
  · exact reflectCoefficients_degree m r Φ hdegree
  · rw [reflectCoefficients_coeff, htop, Polynomial.reflect_monomial]
    simp
end QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients

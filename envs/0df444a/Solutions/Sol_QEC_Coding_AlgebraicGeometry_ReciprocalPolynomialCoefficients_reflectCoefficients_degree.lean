-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:10:17.67272+00:00
-- url     : https://prove2.me/submissions/c39c50ea-b86c-41d3-b8b5-30e7af7f5939

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
theorem _root_.solution (m r : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : Φ.natDegree ≤ r) : (reflectCoefficients m Φ).natDegree ≤ r := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [reflectCoefficients_coeff, Polynomial.natDegree_le_iff_coeff_eq_zero.mp hΦ i hi,
    Polynomial.reflect_zero]
end QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients

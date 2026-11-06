-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:07:37.079104+00:00
-- url     : https://prove2.me/submissions/ee228697-411f-473d-8f06-0dd007e0d3e1

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
theorem _root_.solution (m : ℕ) (Φ : Polynomial (Polynomial k)) (i : ℕ) :
    (reflectCoefficients m Φ).coeff i = (Φ.coeff i).reflect m := by
  rfl
end QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients

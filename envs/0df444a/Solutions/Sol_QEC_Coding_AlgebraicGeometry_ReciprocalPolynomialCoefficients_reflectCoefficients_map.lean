-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:03.730316+00:00
-- url     : https://prove2.me/submissions/2fb7571c-ee42-49e2-8035-d2b0bd9657dd

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
theorem _root_.solution (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z : k) (hz : z ≠ 0) :
    (reflectCoefficients m Φ).map (Polynomial.evalRingHom z⁻¹) * Polynomial.C (z^m) =
      Φ.map (Polynomial.evalRingHom z) := by
  let : Invertible z := invertibleOfNonzero hz
  ext i
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, reflectCoefficients_coeff,
    Polynomial.coeff_map]
  simpa only [Polynomial.coe_evalRingHom, Polynomial.eval₂_id, invOf_eq_inv] using
    Polynomial.eval₂_reflect_mul_pow (RingHom.id k) z m (Φ.coeff i) (hΦ i)
end QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_map_field
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:11:30.732443+00:00
-- url     : https://prove2.me/submissions/4c27f102-eefd-4cd4-ab8b-a45ec79470d0

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_coeff

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
theorem _root_.solution {L : Type*} [Field L]
    (φ : k →+* L) (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z : L) (hz : z ≠ 0) :
    (reflectCoefficients m Φ).map (Polynomial.eval₂RingHom φ z⁻¹) * Polynomial.C (z^m) =
      Φ.map (Polynomial.eval₂RingHom φ z) := by
  let : Invertible z := invertibleOfNonzero hz
  ext i
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, reflectCoefficients_coeff,
    Polynomial.coeff_map]
  simpa only [Polynomial.coe_eval₂RingHom, invOf_eq_inv] using
    Polynomial.eval₂_reflect_mul_pow φ z m (Φ.coeff i) (hΦ i)
end QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients

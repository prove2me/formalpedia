-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients.reflectCoefficients_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:14.746937+00:00
-- url     : https://prove2.me/submissions/89e5f6ff-4cfa-482c-896a-34da5b4b49f9

import Mathlib.Algebra.Polynomial.Reverse
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ReciprocalPolynomialCoefficients_reflectCoefficients_map

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
noncomputable section
open scoped Polynomial
variable {k : Type*} [Field k]
namespace QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients
theorem _root_.solution (m : ℕ) (Φ : Polynomial (Polynomial k))
    (hΦ : ∀ i : ℕ, (Φ.coeff i).natDegree ≤ m) (z t : k) (hz : z ≠ 0)
    (ht : Φ.eval₂ (Polynomial.evalRingHom z) t = 0) :
    (reflectCoefficients m Φ).eval₂ (Polynomial.evalRingHom z⁻¹) t = 0 := by
  have he := congrArg (fun Q : Polynomial k => Q.eval t)
    (reflectCoefficients_map m Φ hΦ z hz)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
    Polynomial.eval_map, ht] at he
  exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ hz)
end QEC.Coding.AlgebraicGeometry.ReciprocalPolynomialCoefficients

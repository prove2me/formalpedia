-- Prove2me | solution 1 for ThreeSum.Karatsuba.length_multiply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:20.601556+00:00
-- url     : https://prove2.me/submissions/e682736c-417e-4bff-be7f-b8a52bd721bc

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Karatsuba
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.Karatsuba
theorem _root_.solution (k : ℕ) (as bs : List ℤ) :
    (multiply k as bs).length ≤ 2 * 2 ^ k := by
  induction k generalizing as bs with
  | zero => simp [multiply]
  | succ k ih =>
    simp only [multiply, length_plus, length_shift, length_minus, pow_succ]
    have h0 := ih (as.take (2 ^ k)) (bs.take (2 ^ k))
    have h2 := ih (as.drop (2 ^ k)) (bs.drop (2 ^ k))
    have h1 := ih (plus (as.take (2 ^ k)) (as.drop (2 ^ k)))
      (plus (bs.take (2 ^ k)) (bs.drop (2 ^ k)))
    omega
end ThreeSum.Karatsuba

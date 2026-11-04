-- Prove2me | solution 1 for ThreeSum.Karatsuba.nodeWork_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:17.095351+00:00
-- url     : https://prove2.me/submissions/031e4e95-1b2c-4cb9-be16-a6a6c3463ef4

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
import Theorems.Thm_ThreeSum_Karatsuba_length_multiply
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
theorem _root_.solution (k : ℕ) (as bs : List ℤ) : nodeWork k as bs ≤ 80 * 2 ^ k := by
  have h0 := length_multiply k (as.take (2 ^ k)) (bs.take (2 ^ k))
  have h2 := length_multiply k (as.drop (2 ^ k)) (bs.drop (2 ^ k))
  have h1 := length_multiply k (plus (as.take (2 ^ k)) (as.drop (2 ^ k)))
    (plus (bs.take (2 ^ k)) (bs.drop (2 ^ k)))
  have hpow : k < 2 ^ k := Nat.lt_two_pow_self
  have hn : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  have hat : (as.take (2 ^ k)).length ≤ 2 ^ k := by simp
  have hbt : (bs.take (2 ^ k)).length ≤ 2 ^ k := by simp
  simp only [nodeWork, splitWork, plusWork, minusWork, negateWork, shiftWork,
    length_negate, length_minus, length_shift, length_plus]
  omega
end ThreeSum.Karatsuba

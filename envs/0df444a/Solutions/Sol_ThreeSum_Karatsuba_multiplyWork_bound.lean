-- Prove2me | solution 1 for ThreeSum.Karatsuba.multiplyWork_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:38:51.812212+00:00
-- url     : https://prove2.me/submissions/b40e9a98-cae1-4da1-b8bb-0022daa35ced

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
import Theorems.Thm_ThreeSum_Karatsuba_nodeWork_le
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
    multiplyWork k as bs + 80 * 2 ^ k ≤ 83 * 3 ^ k := by
  induction k generalizing as bs with
  | zero => simp [multiplyWork]
  | succ k ih =>
    have h0 := ih (as.take (2 ^ k)) (bs.take (2 ^ k))
    have h2 := ih (as.drop (2 ^ k)) (bs.drop (2 ^ k))
    have h1 := ih (plus (as.take (2 ^ k)) (as.drop (2 ^ k)))
      (plus (bs.take (2 ^ k)) (bs.drop (2 ^ k)))
    have hw := nodeWork_le k as bs
    simp only [multiplyWork, pow_succ]
    omega
end ThreeSum.Karatsuba

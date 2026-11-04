-- Prove2me | solution 1 for ThreeSum.Karatsuba.coefficient_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:38:50.465963+00:00
-- url     : https://prove2.me/submissions/f823312f-8a06-46f3-b47a-bd88ec9d57c3

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Karatsuba
import Theorems.Thm_ThreeSum_Karatsuba_multiply_correct

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.Karatsuba
theorem _root_.solution (k : ℕ) (as bs : List ℤ)
    (ha : as.length ≤ 2 ^ k) (hb : bs.length ≤ 2 ^ k) (j : ℕ) :
    (asPolynomial (multiply k as bs)).coeff j =
      ∑ p ∈ Finset.antidiagonal j,
        (asPolynomial as).coeff p.1 * (asPolynomial bs).coeff p.2 := by
  rw [multiply_correct k as bs ha hb, Polynomial.coeff_mul]
end ThreeSum.Karatsuba

-- Prove2me | solution 1 for ThreeSum.Karatsuba.asPolynomial_plus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:19:59.93389+00:00
-- url     : https://prove2.me/submissions/a0b7c8ab-7eea-4dd2-b609-790a4d3cff94

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
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_shift

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.Karatsuba
theorem _root_.solution (as bs : List ℤ) :
    asPolynomial (plus as bs) = asPolynomial as + asPolynomial bs := by
  induction as generalizing bs with
  | nil => simp [plus, asPolynomial]
  | cons a as ih =>
    cases bs with
    | nil => simp [plus, asPolynomial]
    | cons b bs =>
      simp only [plus, asPolynomial, ih, map_add]
      ring
end ThreeSum.Karatsuba

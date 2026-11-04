-- Prove2me | solution 1 for ThreeSum.Karatsuba.asPolynomial_negate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:23:18.712536+00:00
-- url     : https://prove2.me/submissions/e5914089-75a7-4f46-bfa0-fbca355da5f9

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
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.Karatsuba
theorem _root_.solution (as : List ℤ) :
    asPolynomial (negate as) = -asPolynomial as := by
  induction as with
  | nil => simp [negate, asPolynomial]
  | cons a as ih =>
    simp only [negate, List.map_cons, asPolynomial, map_neg]
    change -C a + X * asPolynomial (negate as) = _
    rw [ih]
    ring
end ThreeSum.Karatsuba

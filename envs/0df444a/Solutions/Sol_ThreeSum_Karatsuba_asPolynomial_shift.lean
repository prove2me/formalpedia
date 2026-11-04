-- Prove2me | solution 1 for ThreeSum.Karatsuba.asPolynomial_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:35:16.351472+00:00
-- url     : https://prove2.me/submissions/3d3a8ded-c372-4459-80a1-9c8b7f1d0e30

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
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.Karatsuba
theorem _root_.solution (n : ℕ) (as : List ℤ) :
    asPolynomial (shift n as) = X ^ n * asPolynomial as := by
  induction n with
  | zero => simp [shift]
  | succ n ih =>
    simp only [shift, List.replicate_succ, List.cons_append, asPolynomial, map_zero,
      zero_add]
    change X * asPolynomial (shift n as) = _
    rw [ih, pow_succ]
    ring
end ThreeSum.Karatsuba

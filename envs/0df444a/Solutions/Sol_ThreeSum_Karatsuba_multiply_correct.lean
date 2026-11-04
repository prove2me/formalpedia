-- Prove2me | solution 1 for ThreeSum.Karatsuba.multiply_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:36:53.997233+00:00
-- url     : https://prove2.me/submissions/94ba019c-1ed9-4cfe-ad2a-a30eac7db3a3

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
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_split
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_head
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
theorem _root_.solution (k : ℕ) (as bs : List ℤ)
    (ha : as.length ≤ 2 ^ k) (hb : bs.length ≤ 2 ^ k) :
    asPolynomial (multiply k as bs) = asPolynomial as * asPolynomial bs := by
  induction k generalizing as bs with
  | zero =>
    simp only [pow_zero] at ha hb
    simp only [multiply, asPolynomial, mul_zero, add_zero]
    rw [asPolynomial_head ha, asPolynomial_head hb, map_mul]
  | succ k ih =>
    have ha0 : (as.take (2 ^ k)).length ≤ 2 ^ k := by simp
    have hb0 : (bs.take (2 ^ k)).length ≤ 2 ^ k := by simp
    have ha1 : (as.drop (2 ^ k)).length ≤ 2 ^ k := by
      simp only [List.length_drop]
      simp only [pow_succ] at ha
      omega
    have hb1 : (bs.drop (2 ^ k)).length ≤ 2 ^ k := by
      simp only [List.length_drop]
      simp only [pow_succ] at hb
      omega
    have hap : (plus (as.take (2 ^ k)) (as.drop (2 ^ k))).length ≤ 2 ^ k := by
      simpa using max_le ha0 ha1
    have hbp : (plus (bs.take (2 ^ k)) (bs.drop (2 ^ k))).length ≤ 2 ^ k := by
      simpa using max_le hb0 hb1
    simp only [multiply, asPolynomial_plus, asPolynomial_shift, asPolynomial_minus]
    rw [ih _ _ ha0 hb0, ih _ _ ha1 hb1, ih _ _ hap hbp,
      asPolynomial_plus, asPolynomial_plus]
    conv_rhs => rw [asPolynomial_split (2 ^ k) as, asPolynomial_split (2 ^ k) bs]
    ring
end ThreeSum.Karatsuba

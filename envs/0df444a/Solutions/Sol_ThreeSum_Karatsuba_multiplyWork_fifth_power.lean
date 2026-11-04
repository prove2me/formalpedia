-- Prove2me | solution 1 for ThreeSum.Karatsuba.multiplyWork_fifth_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:35.170898+00:00
-- url     : https://prove2.me/submissions/27c7f79d-909a-4f5c-bf42-9307ce13fc1e

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
import Theorems.Thm_ThreeSum_Karatsuba_multiplyWork_le
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
    multiplyWork k as bs ^ 5 ≤ 83 ^ 5 * (2 ^ k) ^ 8 := by
  have hw := Nat.pow_le_pow_left (multiplyWork_le k as bs) 5
  have hbase : (3 : ℕ) ^ 5 ≤ 2 ^ 8 := by norm_num
  have hp := Nat.pow_le_pow_left hbase k
  have hp' : (3 ^ k) ^ 5 ≤ (2 ^ k) ^ 8 := by
    simpa only [← pow_mul, Nat.mul_comm] using hp
  calc
    multiplyWork k as bs ^ 5 ≤ (83 * 3 ^ k) ^ 5 := hw
    _ = 83 ^ 5 * (3 ^ k) ^ 5 := by rw [mul_pow]
    _ ≤ 83 ^ 5 * (2 ^ k) ^ 8 := Nat.mul_le_mul_left _ hp'
end ThreeSum.Karatsuba

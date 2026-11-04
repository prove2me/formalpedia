-- Prove2me | solution 1 for ThreeSum.Karatsuba.product_coeff_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:52.293684+00:00
-- url     : https://prove2.me/submissions/6dfaab96-4ff4-4ebb-b56f-61a66a4cb0e0

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_coeffBound_nonneg
import Theorems.Thm_ThreeSum_Karatsuba_product_coeff_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift


attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.Karatsuba.minus_getD

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
open scoped BigOperators
namespace ThreeSum.Karatsuba
theorem _root_.solution {as bs : List ℤ} {n : ℕ} {U : ℤ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) (j : ℕ) :
    |(asPolynomial as * asPolynomial bs).coeff j| ≤ 2 * (n : ℤ) * U ^ 2 := by
  have hU : 0 ≤ U := coeffBound_nonneg hA
  by_cases hj : 2 * n ≤ j
  · rw [product_coeff_zero ha hb hj, abs_zero]
    positivity
  · have hj' : j + 1 ≤ 2 * n := by omega
    rw [Polynomial.coeff_mul]
    calc
      _ ≤ ∑ p ∈ Finset.antidiagonal j,
          |(asPolynomial as).coeff p.1 * (asPolynomial bs).coeff p.2| :=
        Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ _p ∈ Finset.antidiagonal j, U ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul, asPolynomial_coeff, asPolynomial_coeff, pow_two]
        exact mul_le_mul (hA p.1) (hB p.2) (abs_nonneg _) hU
      _ = (j + 1 : ℕ) * U ^ 2 := by simp
      _ ≤ 2 * (n : ℤ) * U ^ 2 := by
        have hjR : (j + 1 : ℕ) ≤ (2 * (n : ℤ)) := by exact_mod_cast hj'
        exact mul_le_mul_of_nonneg_right hjR (sq_nonneg U)
end ThreeSum.Karatsuba

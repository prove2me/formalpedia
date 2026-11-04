-- Prove2me | solution 1 for ThreeSum.Karatsuba.product_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:19.231349+00:00
-- url     : https://prove2.me/submissions/8eb34b4e-5761-4090-9545-dbd4ac73985b

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
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

set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
open scoped BigOperators
namespace ThreeSum.Karatsuba
theorem _root_.solution {as bs : List ℤ} {n j : ℕ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n) (hj : 2 * n ≤ j) :
    (asPolynomial as * asPolynomial bs).coeff j = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Finset.mem_antidiagonal.mp hp
  by_cases hpa : n ≤ p.1
  · rw [asPolynomial_coeff, List.getD_eq_default _ _ (ha.trans hpa), zero_mul]
  · have hpb : n ≤ p.2 := by omega
    rw [asPolynomial_coeff bs, List.getD_eq_default _ _ (hb.trans hpb), mul_zero]
end ThreeSum.Karatsuba

-- Prove2me | solution 1 for ThreeSum.Karatsuba.CoeffBound.mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:50.333825+00:00
-- url     : https://prove2.me/submissions/7ff27afe-acbc-4ce5-897c-ea7712c6a2db

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
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
namespace CoeffBound
theorem _root_.solution {as : List ℤ} {U x : ℤ} (h : CoeffBound as U)
    (hx : x ∈ as) : |x| ≤ U := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  simpa only [List.getD_eq_getElem _ _ hj] using h j
end CoeffBound
end ThreeSum.Karatsuba

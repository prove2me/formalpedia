-- Prove2me | solution 1 for ThreeSum.KaratsubaInterface.pad_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:33.523898+00:00
-- url     : https://prove2.me/submissions/c22f1622-9b8f-4e15-91b7-411bc9b28df2

import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Mathlib.Data.Nat.Log
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Theorems.Thm_ThreeSum_KaratsubaInterface_polynomial_pad
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff



set_option autoImplicit false
open ThreeSum ThreeSum.KaratsubaInterface
open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial
namespace ThreeSum.KaratsubaInterface
theorem _root_.solution {n : ℕ} {as : List ℤ} {U : ℤ} (hA : CoeffBound as U) :
    CoeffBound (pad n as) U := by
  intro j
  rw [← asPolynomial_coeff, polynomial_pad, asPolynomial_coeff]
  exact hA j
end ThreeSum.KaratsubaInterface

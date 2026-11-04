-- Prove2me | solution 1 for ThreeSum.Auxiliary.moduli_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:41.755377+00:00
-- url     : https://prove2.me/submissions/f7f5c96c-a307-49dc-9064-b73eb8f07607

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators
namespace ThreeSum.Auxiliary
theorem _root_.solution (C : Finset ℕ) :
    (∏ p ∈ moduli C, p) = (∏ p ∈ C, p : ℕ) := by
  rw [moduli, Finset.prod_image]
  · simp
  · intro p hp q hq hpq
    exact Nat.cast_injective hpq
end ThreeSum.Auxiliary

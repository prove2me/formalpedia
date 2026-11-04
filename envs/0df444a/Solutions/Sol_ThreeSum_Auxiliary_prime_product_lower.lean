-- Prove2me | solution 1 for ThreeSum.Auxiliary.prime_product_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:40.600043+00:00
-- url     : https://prove2.me/submissions/3eb05ba6-cb35-4b2a-a275-35ef626d1461

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
theorem _root_.solution (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p) :
    2 ^ C.card ≤ ∏ p ∈ C, p := by
  calc
    2 ^ C.card = ∏ _p ∈ C, 2 := by simp
    _ ≤ ∏ p ∈ C, p := prod_le_prod' (fun p hp => (hC p hp).two_le)
end ThreeSum.Auxiliary

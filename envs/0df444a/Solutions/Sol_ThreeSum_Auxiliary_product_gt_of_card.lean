-- Prove2me | solution 1 for ThreeSum.Auxiliary.product_gt_of_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:57.305281+00:00
-- url     : https://prove2.me/submissions/68f47c24-70a8-43d7-b6a4-18158c4b5d0b

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
import Theorems.Thm_ThreeSum_Auxiliary_prime_product_lower

set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators
namespace ThreeSum.Auxiliary
theorem _root_.solution (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    (M : ℕ) (hcard : Nat.log 2 M < C.card) : M < ∏ p ∈ C, p := by
  exact (Nat.lt_pow_succ_log_self (by decide : 1 < 2) M).trans_le
    ((Nat.pow_le_pow_right (by decide : 1 ≤ 2) hcard).trans (prime_product_lower C hC))
end ThreeSum.Auxiliary

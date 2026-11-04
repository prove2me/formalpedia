-- Prove2me | solution 1 for ThreeSum.Auxiliary.candidate_pool_separates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:59.693786+00:00
-- url     : https://prove2.me/submissions/1cdcf831-c52a-4139-ab92-3082612a78b9

import Definitions.Def_Submission_ThreeSum_PrimeChain
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Mathlib.RingTheory.Coprime.Lemmas
import Definitions.Def_Submission_ThreeSum_Auxiliary
import Theorems.Thm_ThreeSum_Auxiliary_product_gt_of_card
import Theorems.Thm_ThreeSum_Auxiliary_separates_nonzero
import Theorems.Thm_ThreeSum_PrimeDensity_mem_candidates


set_option autoImplicit false
open ThreeSum ThreeSum.Auxiliary
open Finset
open scoped BigOperators
namespace ThreeSum.Auxiliary
theorem _root_.solution (y M : ℕ)
    (hcard : Nat.log 2 M < (PrimeDensity.candidates y).card)
    {z : ℤ} (hz : z ≠ 0) (hbound : z.natAbs ≤ M) :
    ∃ p ∈ moduli (PrimeDensity.candidates y), ¬p ∣ z := by
  have hprime : ∀ p ∈ PrimeDensity.candidates y, Nat.Prime p :=
    fun p hp => (PrimeDensity.mem_candidates.mp hp).1
  exact separates_nonzero _ hprime (product_gt_of_card _ hprime M hcard) hz hbound
end ThreeSum.Auxiliary

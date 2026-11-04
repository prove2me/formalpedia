-- Prove2me | solution 1 for ThreeSum.TernaryPairedRecurrence.zero_of_iterated_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:54.149242+00:00
-- url     : https://prove2.me/submissions/c2af5eb0-a974-443c-b652-6476813c5f93

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Theorems.Thm_ThreeSum_TernaryPairedRecurrence_iterate_bound

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence
namespace ThreeSum.TernaryPairedRecurrence
theorem _root_.solution (a b : ℕ) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1) ≤ b*score j) (r : ℕ)
    (hsmall : b^r*score 0 < a^r) : score r=0 := by
  have hh := iterate_bound a b score hstep r
  by_contra hn
  have hp : 1 ≤ score r := Nat.pos_of_ne_zero hn
  have hm := Nat.mul_le_mul_left (a^r) hp
  simp only [mul_one] at hm
  omega
end ThreeSum.TernaryPairedRecurrence

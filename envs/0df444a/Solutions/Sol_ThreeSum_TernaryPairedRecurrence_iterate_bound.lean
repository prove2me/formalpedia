-- Prove2me | solution 1 for ThreeSum.TernaryPairedRecurrence.iterate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:47.976647+00:00
-- url     : https://prove2.me/submissions/4c1353a2-1023-4522-9c4a-fbaa62a64dda

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence
namespace ThreeSum.TernaryPairedRecurrence
theorem _root_.solution (a b : ℕ) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1) ≤ b*score j) (r : ℕ) :
    a^r*score r ≤ b^r*score 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      _ = a^r*(a*score (r+1)) := by rw [pow_succ]; ring
      _ ≤ a^r*(b*score r) := Nat.mul_le_mul_left _ (hstep r)
      _ = b*(a^r*score r) := by ring
      _ ≤ b*(b^r*score 0) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ring
end ThreeSum.TernaryPairedRecurrence

-- Prove2me | solution 1 for ThreeSum.TernaryPairedRecurrence.weighted_iteration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:37.227169+00:00
-- url     : https://prove2.me/submissions/810679e5-46f6-425e-a343-7a86477e1f20

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence
namespace ThreeSum.TernaryPairedRecurrence
theorem _root_.solution (a b c : ℕ) (ha : 0<a) (score : ℕ → ℕ)
    (hstep : ∀ j, a*score (j+1)≤b*score j) (hbudget : b*c≤a) (r : ℕ) :
    c^r*score r≤score 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    apply Nat.le_of_mul_le_mul_left (c := a) ?_ ha
    calc
      _ = c^r*c*(a*score (r+1)) := by rw [pow_succ]; ring
      _ ≤ c^r*c*(b*score r) := Nat.mul_le_mul_left _ (hstep r)
      _ = (b*c)*(c^r*score r) := by ring
      _ ≤ a*(c^r*score r) := Nat.mul_le_mul_right _ hbudget
      _ ≤ _ := Nat.mul_le_mul_left _ ih
end ThreeSum.TernaryPairedRecurrence

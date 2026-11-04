-- Prove2me | solution 1 for ThreeSum.BinarySearch.upperSearch_correct_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:10.298663+00:00
-- url     : https://prove2.me/submissions/419487b4-fabc-47e2-9351-44b33052b5f4

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_BinarySearch

set_option autoImplicit false
open ThreeSum ThreeSum.BinarySearch
namespace ThreeSum.BinarySearch
theorem _root_.solution (f : ℕ → ℤ) (x : ℤ) (n fuel lo hi : ℕ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j)
    (hlo : lo ≤ hi) (hhi : hi ≤ n) (hwidth : hi - lo < 2 ^ fuel)
    (hlower : ∀ i < lo, f i ≤ x)
    (hupper : ∀ i, hi ≤ i → i < n → x < f i) :
    Partition f x n (upperSearch f x fuel lo hi) := by
  induction fuel generalizing lo hi with
  | zero =>
      have heq : lo = hi := by simp only [Nat.pow_zero] at hwidth; omega
      simpa only [Partition, upperSearch, heq] using And.intro hhi (And.intro (heq ▸ hlower) hupper)
  | succ fuel ih =>
      rw [upperSearch]
      split
      · rename_i hlt
        dsimp only
        let mid := (lo + hi) / 2
        have hmidlo : lo ≤ mid := by dsimp [mid]; omega
        have hmidhi : mid < hi := by dsimp [mid]; omega
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by
          rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow] at hwidth
        by_cases htest : f mid ≤ x
        · rw [if_pos htest]
          apply ih (mid + 1) hi (by omega) hhi
          · dsimp [mid] at *; omega
          · intro i hi'
            exact le_trans (hsorted i mid (by omega) (by omega)) htest
          · exact hupper
        · rw [if_neg htest]
          apply ih lo mid hmidlo (by omega)
          · dsimp [mid] at *; omega
          · exact hlower
          · intro i hmi hin
            exact lt_of_lt_of_le (by omega : x < f mid) (hsorted mid i hmi hin)
      · rename_i hstop
        have heq : lo = hi := by omega
        simpa only [Partition, heq] using And.intro hhi (And.intro (heq ▸ hlower) hupper)
end ThreeSum.BinarySearch

-- Prove2me | solution 1 for ThreeSum.BinarySearch.upperBound_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:36.645574+00:00
-- url     : https://prove2.me/submissions/80752936-c552-49ac-af79-0e23b93824c2

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_WeightedCache3SUM_Alias_d08fc2f449d67548

set_option autoImplicit false
open ThreeSum ThreeSum.BinarySearch
namespace ThreeSum.BinarySearch
theorem _root_.solution (f : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j) :
    Partition f x n (upperBound f n x) := by
  apply upperSearch_correct f x n (Nat.log 2 n + 1) 0 n hsorted (by omega) (by omega)
  · simpa only [Nat.sub_zero] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · intro i hi; omega
  · intro i hi hin; omega
end ThreeSum.BinarySearch

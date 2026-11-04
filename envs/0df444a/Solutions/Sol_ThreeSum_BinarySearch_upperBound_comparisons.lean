-- Prove2me | solution 1 for ThreeSum.BinarySearch.upperBound_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:35:53.691466+00:00
-- url     : https://prove2.me/submissions/02a78c94-437c-4156-946d-1d75d37d45a7

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Theorems.Thm_ThreeSum_BinarySearch_comparisons_le

set_option autoImplicit false
open ThreeSum ThreeSum.BinarySearch
namespace ThreeSum.BinarySearch
theorem _root_.solution (f : ℕ → ℤ) (n : ℕ) (x : ℤ) :
    comparisons f x (Nat.log 2 n + 1) 0 n ≤ Nat.log 2 n + 1 :=
  comparisons_le f x _ _ _
end ThreeSum.BinarySearch

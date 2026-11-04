-- Prove2me | solution 1 for ThreeSum.BinarySearch.comparisons_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:12.536933+00:00
-- url     : https://prove2.me/submissions/1de73959-451d-46fe-9d48-10856ca0ccd3

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_BinarySearch

set_option autoImplicit false
open ThreeSum ThreeSum.BinarySearch
namespace ThreeSum.BinarySearch
theorem _root_.solution (f : ℕ → ℤ) (x : ℤ) (fuel lo hi : ℕ) :
    comparisons f x fuel lo hi ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero => simp [comparisons]
  | succ fuel ih =>
      simp only [comparisons]
      split
      · split
        · have h := ih ((lo + hi) / 2 + 1) hi
          omega
        · have h := ih lo ((lo + hi) / 2)
          omega
      · omega
end ThreeSum.BinarySearch

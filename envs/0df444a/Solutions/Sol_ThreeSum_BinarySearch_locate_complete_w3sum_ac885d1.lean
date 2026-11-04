-- Prove2me | solution 1 for ThreeSum.BinarySearch.locate_complete_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:58.168191+00:00
-- url     : https://prove2.me/submissions/142a3027-bd7f-4957-a0db-c51a96e2b9d8

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Theorems.Thm_ThreeSum_BinarySearch_upperBound_correct

set_option autoImplicit false
open ThreeSum ThreeSum.BinarySearch
namespace ThreeSum.BinarySearch
theorem _root_.solution (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hseparated : ∀ i j, i < j → j < n → hi i < lo j)
    {i : ℕ} (hin : i < n) (hil : lo i ≤ x) (hih : x ≤ hi i) :
    locate lo hi n x = some i := by
  have hp := upperBound_correct lo n x hsorted
  rcases hp with ⟨hkn, hpre, hpost⟩
  have hik : i < upperBound lo n x := by
    by_contra hh
    have hh' := hpost i (by omega) hin
    omega
  have heq : upperBound lo n x = i + 1 := by
    by_contra hh
    have hnext : i + 1 < upperBound lo n x := by omega
    have hnl := hpre (i + 1) hnext
    have hnh := hseparated i (i + 1) (by omega) (by omega)
    omega
  simp [locate, heq, hih]
end ThreeSum.BinarySearch

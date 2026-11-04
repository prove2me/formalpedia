-- Prove2me | solution 1 for ThreeSum.BinarySearch.locate_sound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:45.046409+00:00
-- url     : https://prove2.me/submissions/4e601f8f-6f52-4d00-b6a8-824aa0f9ddaf

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
    {i : ℕ} (h : locate lo hi n x = some i) :
    i < n ∧ lo i ≤ x ∧ x ≤ hi i := by
  have hp := upperBound_correct lo n x hsorted
  rcases hp with ⟨hkn, hpre, hpost⟩
  unfold locate at h
  dsimp only at h
  split at h
  · rename_i hk
    split at h
    · rename_i hxh
      have heq : upperBound lo n x - 1 = i := Option.some.inj h
      subst i
      exact ⟨by omega, hpre _ (by omega), hxh⟩
    · cases h
  · cases h
end ThreeSum.BinarySearch

-- Prove2me | solution 1 for ThreeSum.TernaryPairedRecurrence.scaled_step_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:38.367689+00:00
-- url     : https://prove2.me/submissions/1df97db9-3d12-445b-b532-25febfe9961a

import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedRecurrence
namespace ThreeSum.TernaryPairedRecurrence
theorem _root_.solution (a b old next sOld sNext : ℕ)
    (hOld : 0<sOld) (hNext : 0<sNext) :
    a*sOld*(sNext*next)≤b*sNext*(sOld*old) ↔ a*next≤b*old := by
  have heL : a*sOld*(sNext*next)=(sOld*sNext)*(a*next) := by ring
  have heR : b*sNext*(sOld*old)=(sOld*sNext)*(b*old) := by ring
  rw [heL,heR]
  constructor
  · intro h
    exact Nat.le_of_mul_le_mul_left h (Nat.mul_pos hOld hNext)
  · intro h
    exact Nat.mul_le_mul_left _ h
end ThreeSum.TernaryPairedRecurrence

-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.source_natAbs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:23.198401+00:00
-- url     : https://prove2.me/submissions/6bd93881-2473-4be4-9b3c-7924b5618b0f

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
import Theorems.Thm_ThreeSum_TernarySignedModes_leftRaw_abs
import Theorems.Thm_ThreeSum_TernarySignedModes_rightRaw_abs

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {U radix J : ℕ} (hb : 1 < radix)
    (b c : ℤ) (k : Coordinate J) :
    (leftRaw U radix J b k).natAbs ≤ radix ∧
      (rightRaw U radix J c k).natAbs ≤ radix := by
  constructor
  · have h := leftRaw_abs (U := U) hb b k
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · have h := rightRaw_abs (U := U) hb c k
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
end ThreeSum.TernarySignedModes

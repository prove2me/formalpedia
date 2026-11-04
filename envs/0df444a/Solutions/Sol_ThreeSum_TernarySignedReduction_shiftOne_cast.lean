-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.shiftOne_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:42.493767+00:00
-- url     : https://prove2.me/submissions/dba9f533-3b43-4538-a9ed-19ef9bc20209

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution {U : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) :
    (shiftOne U x : ℤ)=x+U := by
  have hl := (abs_le.mp hx).1
  exact Int.toNat_of_nonneg (by omega)
end ThreeSum.TernarySignedReduction

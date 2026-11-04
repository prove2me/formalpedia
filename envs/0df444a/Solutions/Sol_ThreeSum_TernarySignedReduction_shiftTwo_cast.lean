-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.shiftTwo_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:37:43.556474+00:00
-- url     : https://prove2.me/submissions/43351442-7fb0-4f7e-96fb-3d2c68b6c662

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution {U : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) :
    (shiftTwo U x : ℤ)=x+2*U := by
  have hl := (abs_le.mp hx).1
  have hU : (0 : ℤ) ≤ U := Int.natCast_nonneg U
  exact Int.toNat_of_nonneg (by omega)
end ThreeSum.TernarySignedReduction

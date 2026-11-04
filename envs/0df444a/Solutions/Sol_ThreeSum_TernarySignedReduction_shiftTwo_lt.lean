-- Prove2me | solution 1 for ThreeSum.TernarySignedReduction.shiftTwo_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:38.73966+00:00
-- url     : https://prove2.me/submissions/1b766d5a-7ebf-4776-b7c9-b9a84c6004a4

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Theorems.Thm_ThreeSum_TernarySignedReduction_shiftTwo_cast

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset
namespace ThreeSum.TernarySignedReduction
theorem _root_.solution {U b J : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) (hcap : 4*U<b^J) :
    shiftTwo U x<b^J := by
  have hu := (abs_le.mp hx).2
  have hh : (4 : ℤ)*U < (b^J : ℕ) := by exact_mod_cast hcap
  have hU : (0 : ℤ) ≤ U := Int.natCast_nonneg U
  have hc := shiftTwo_cast hx
  exact_mod_cast (by omega : (shiftTwo U x : ℤ)<(b^J : ℕ))
end ThreeSum.TernarySignedReduction

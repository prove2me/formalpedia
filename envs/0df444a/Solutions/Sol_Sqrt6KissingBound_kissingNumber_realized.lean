-- Prove2me | solution 1 for Sqrt6KissingBound.kissingNumber_realized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:28:27.341522+00:00
-- url     : https://prove2.me/submissions/5807a6f2-51e5-489b-9b43-fff5caa2c586

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
import Theorems.Thm_Sqrt6KissingBound_realizableKissingCard_zero

set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
namespace Sqrt6KissingBound
theorem _root_.solution (n : ℕ) :
    RealizableKissingCard n (kissingNumber n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (realizableKissingCard_zero n)
end Sqrt6KissingBound

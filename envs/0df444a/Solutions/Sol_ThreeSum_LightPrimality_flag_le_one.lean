-- Prove2me | solution 1 for ThreeSum.LightPrimality.flag_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:07.175756+00:00
-- url     : https://prove2.me/submissions/920aeb34-aa27-47e3-b64b-566bc254f614

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
import Theorems.Thm_ThreeSum_LightPrimality_flag_zero_or_one

set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace ThreeSum.LightPrimality
theorem _root_.solution (n i : ℕ) : flag n i ≤ 1 := by
  rcases flag_zero_or_one n i with h | h <;> omega
end ThreeSum.LightPrimality

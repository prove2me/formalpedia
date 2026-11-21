-- Prove2me | solution 1 for RH1E6S04.group_085
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:08:07.022057+00:00
-- url     : https://prove2.me/submissions/22441c1e-b992-4c2e-b19d-349549c4fe19

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_085_0
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_085 : RS5.BandZeros ((22937497748 : ℝ) / 65536) ((22937600000 : ℝ) / 65536) 3 := by
  exact part_085_0
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22937497748 : ℝ) / 65536) ((22937600000 : ℝ) / 65536) 3 := by
  apply RH1E6S04.group_085 <;> assumption

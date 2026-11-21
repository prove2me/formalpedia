-- Prove2me | solution 1 for RH1E6S05.group_086
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:17:26.996606+00:00
-- url     : https://prove2.me/submissions/8dfdda18-9110-4974-98e5-c306a6f3f53d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_086_0
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_086 : RS5.BandZeros ((26209659216 : ℝ) / 65536) ((26214400000 : ℝ) / 65536) 128 := by
  exact part_086_0
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((26209659216 : ℝ) / 65536) ((26214400000 : ℝ) / 65536) 128 := by
  apply RH1E6S05.group_086 <;> assumption

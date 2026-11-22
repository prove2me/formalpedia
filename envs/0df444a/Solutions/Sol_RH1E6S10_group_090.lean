-- Prove2me | solution 1 for RH1E6S10.group_090
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:06:37.779484+00:00
-- url     : https://prove2.me/submissions/949b9e81-9953-4909-96b5-9a772542aa69

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_090_0
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_090 : RS5.BandZeros ((42593680676 : ℝ) / 65536) ((42598400000 : ℝ) / 65536) 132 := by
  exact part_090_0
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42593680676 : ℝ) / 65536) ((42598400000 : ℝ) / 65536) 132 := by
  apply RH1E6S10.group_090 <;> assumption

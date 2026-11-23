-- Prove2me | solution 1 for RH1E6S16.group_093
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:40:39.018203+00:00
-- url     : https://prove2.me/submissions/51da5beb-58a4-4c44-9605-abdc884cdd95

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_093_0
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_093 : RS5.BandZeros ((62252083202 : ℝ) / 65536) ((62259200000 : ℝ) / 65536) 206 := by
  exact part_093_0
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62252083202 : ℝ) / 65536) ((62259200000 : ℝ) / 65536) 206 := by
  apply RH1E6S16.group_093 <;> assumption

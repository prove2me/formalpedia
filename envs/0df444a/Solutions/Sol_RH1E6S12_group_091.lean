-- Prove2me | solution 1 for RH1E6S12.group_091
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T17:57:16.350924+00:00
-- url     : https://prove2.me/submissions/9b116a6c-9de7-4783-b064-8b992a0a3ad5

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_091_0
import Theorems.Thm_RH1E6S12_part_091_1
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_091 : RS5.BandZeros ((49141508855 : ℝ) / 65536) ((49152000000 : ℝ) / 65536) 298 := by
  have g0 := part_091_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_091_1
  exact g1
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((49141508855 : ℝ) / 65536) ((49152000000 : ℝ) / 65536) 298 := by
  apply RH1E6S12.group_091 <;> assumption

-- Prove2me | solution 1 for RH1E6S16.group_091
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:40:35.019801+00:00
-- url     : https://prove2.me/submissions/a9b78618-ee71-491d-97d4-ff9666d388ab

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_091_0
import Theorems.Thm_RH1E6S16_part_091_1
import Theorems.Thm_RH1E6S16_part_091_2
import Theorems.Thm_RH1E6S16_part_091_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_091 : RS5.BandZeros ((62181921357 : ℝ) / 65536) ((62217004170 : ℝ) / 65536) 1016 := by
  have g0 := part_091_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_091_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_091_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_091_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62181921357 : ℝ) / 65536) ((62217004170 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_091 <;> assumption

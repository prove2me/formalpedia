-- Prove2me | solution 1 for RH1E6S16.group_090
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T19:37:26.967937+00:00
-- url     : https://prove2.me/submissions/c3e7c68f-94a9-4bf7-a91a-29131603f05d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_090_0
import Theorems.Thm_RH1E6S16_part_090_1
import Theorems.Thm_RH1E6S16_part_090_2
import Theorems.Thm_RH1E6S16_part_090_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_090 : RS5.BandZeros ((62146845417 : ℝ) / 65536) ((62181921357 : ℝ) / 65536) 1016 := by
  have g0 := part_090_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_090_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_090_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_090_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((62146845417 : ℝ) / 65536) ((62181921357 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_090 <;> assumption

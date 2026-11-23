-- Prove2me | solution 1 for RH1E6S16.group_049
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T17:10:35.330549+00:00
-- url     : https://prove2.me/submissions/92d35047-cae1-41ef-a3dd-67da424b7b21

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_049_0
import Theorems.Thm_RH1E6S16_part_049_1
import Theorems.Thm_RH1E6S16_part_049_2
import Theorems.Thm_RH1E6S16_part_049_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_049 : RS5.BandZeros ((60706974893 : ℝ) / 65536) ((60742138517 : ℝ) / 65536) 1016 := by
  have g0 := part_049_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_049_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_049_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_049_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60706974893 : ℝ) / 65536) ((60742138517 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_049 <;> assumption

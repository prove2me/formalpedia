-- Prove2me | solution 1 for RH1E6S16.group_041
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T16:39:56.791403+00:00
-- url     : https://prove2.me/submissions/63d8588b-706c-4459-a92b-c76f9081667d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_041_0
import Theorems.Thm_RH1E6S16_part_041_1
import Theorems.Thm_RH1E6S16_part_041_2
import Theorems.Thm_RH1E6S16_part_041_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_041 : RS5.BandZeros ((60425708772 : ℝ) / 65536) ((60460855515 : ℝ) / 65536) 1016 := by
  have g0 := part_041_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_041_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_041_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_041_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60425708772 : ℝ) / 65536) ((60460855515 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_041 <;> assumption

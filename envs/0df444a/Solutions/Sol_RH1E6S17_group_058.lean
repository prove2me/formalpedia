-- Prove2me | solution 1 for RH1E6S17.group_058
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:07:19.365699+00:00
-- url     : https://prove2.me/submissions/fd0cd5b0-c612-4d5b-a8ec-b4e328f91fd1

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_058_0
import Theorems.Thm_RH1E6S17_part_058_1
import Theorems.Thm_RH1E6S17_part_058_2
import Theorems.Thm_RH1E6S17_part_058_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_058 : RS5.BandZeros ((64291040583 : ℝ) / 65536) ((64326015904 : ℝ) / 65536) 1016 := by
  have g0 := part_058_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_058_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_058_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_058_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64291040583 : ℝ) / 65536) ((64326015904 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_058 <;> assumption

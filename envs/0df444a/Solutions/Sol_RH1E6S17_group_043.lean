-- Prove2me | solution 1 for RH1E6S17.group_043
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:13:16.739802+00:00
-- url     : https://prove2.me/submissions/e4a2e64d-1ab3-43f7-88a7-c4d1c37cfde3

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_043_0
import Theorems.Thm_RH1E6S17_part_043_1
import Theorems.Thm_RH1E6S17_part_043_2
import Theorems.Thm_RH1E6S17_part_043_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_043 : RS5.BandZeros ((63766090001 : ℝ) / 65536) ((63801080696 : ℝ) / 65536) 1016 := by
  have g0 := part_043_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_043_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_043_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_043_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63766090001 : ℝ) / 65536) ((63801080696 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_043 <;> assumption

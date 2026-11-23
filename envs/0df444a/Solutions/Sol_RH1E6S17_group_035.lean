-- Prove2me | solution 1 for RH1E6S17.group_035
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:44:54.560975+00:00
-- url     : https://prove2.me/submissions/76910a67-b1e7-4843-aeb6-3ab7010dc63b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_035_0
import Theorems.Thm_RH1E6S17_part_035_1
import Theorems.Thm_RH1E6S17_part_035_2
import Theorems.Thm_RH1E6S17_part_035_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_035 : RS5.BandZeros ((63485960006 : ℝ) / 65536) ((63520972210 : ℝ) / 65536) 1016 := by
  have g0 := part_035_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_035_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_035_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_035_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63485960006 : ℝ) / 65536) ((63520972210 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_035 <;> assumption

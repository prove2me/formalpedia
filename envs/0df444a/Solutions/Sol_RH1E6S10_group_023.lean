-- Prove2me | solution 1 for RH1E6S10.group_023
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:31:45.360403+00:00
-- url     : https://prove2.me/submissions/9b5a2758-04c5-4992-a1a8-9bf88ada276b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_023_0
import Theorems.Thm_RH1E6S10_part_023_1
import Theorems.Thm_RH1E6S10_part_023_2
import Theorems.Thm_RH1E6S10_part_023_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_023 : RS5.BandZeros ((40159987027 : ℝ) / 65536) ((40196412264 : ℝ) / 65536) 1016 := by
  have g0 := part_023_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_023_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_023_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_023_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40159987027 : ℝ) / 65536) ((40196412264 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_023 <;> assumption

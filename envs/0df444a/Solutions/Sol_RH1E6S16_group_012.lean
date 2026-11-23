-- Prove2me | solution 1 for RH1E6S16.group_012
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:53:24.449811+00:00
-- url     : https://prove2.me/submissions/4fb58b48-82dc-4e82-b436-538310d0560d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_012_0
import Theorems.Thm_RH1E6S16_part_012_1
import Theorems.Thm_RH1E6S16_part_012_2
import Theorems.Thm_RH1E6S16_part_012_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_012 : RS5.BandZeros ((59405126319 : ℝ) / 65536) ((59440335697 : ℝ) / 65536) 1016 := by
  have g0 := part_012_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_012_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_012_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_012_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59405126319 : ℝ) / 65536) ((59440335697 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_012 <;> assumption

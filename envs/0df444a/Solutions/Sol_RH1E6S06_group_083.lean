-- Prove2me | solution 1 for RH1E6S06.group_083
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:46:30.996517+00:00
-- url     : https://prove2.me/submissions/ca855e7e-dbd4-4be5-9c15-bbbbc2cb30a9

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_083_0
import Theorems.Thm_RH1E6S06_part_083_1
import Theorems.Thm_RH1E6S06_part_083_2
import Theorems.Thm_RH1E6S06_part_083_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_083 : RS5.BandZeros ((29337467061 : ℝ) / 65536) ((29374896224 : ℝ) / 65536) 1016 := by
  have g0 := part_083_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_083_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_083_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_083_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29337467061 : ℝ) / 65536) ((29374896224 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_083 <;> assumption

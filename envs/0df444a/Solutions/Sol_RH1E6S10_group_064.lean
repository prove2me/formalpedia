-- Prove2me | solution 1 for RH1E6S10.group_064
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:01:46.174916+00:00
-- url     : https://prove2.me/submissions/6e60e0ee-c21d-44ed-8042-172ef2ed2c4a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_064_0
import Theorems.Thm_RH1E6S10_part_064_1
import Theorems.Thm_RH1E6S10_part_064_2
import Theorems.Thm_RH1E6S10_part_064_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_064 : RS5.BandZeros ((41650734042 : ℝ) / 65536) ((41687044137 : ℝ) / 65536) 1016 := by
  have g0 := part_064_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_064_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_064_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_064_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41650734042 : ℝ) / 65536) ((41687044137 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_064 <;> assumption

-- Prove2me | solution 1 for RH1E6S10.group_058
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:44:51.672279+00:00
-- url     : https://prove2.me/submissions/866ecb7f-c739-4685-86e5-1726e530af45

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_058_0
import Theorems.Thm_RH1E6S10_part_058_1
import Theorems.Thm_RH1E6S10_part_058_2
import Theorems.Thm_RH1E6S10_part_058_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_058 : RS5.BandZeros ((41432869299 : ℝ) / 65536) ((41469186982 : ℝ) / 65536) 1016 := by
  have g0 := part_058_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_058_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_058_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_058_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41432869299 : ℝ) / 65536) ((41469186982 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_058 <;> assumption

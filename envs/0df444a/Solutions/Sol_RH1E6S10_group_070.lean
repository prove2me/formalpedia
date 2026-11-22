-- Prove2me | solution 1 for RH1E6S10.group_070
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:15:43.777292+00:00
-- url     : https://prove2.me/submissions/a8152e8c-45af-4c18-8ef3-fa8fda45b74b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_070_0
import Theorems.Thm_RH1E6S10_part_070_1
import Theorems.Thm_RH1E6S10_part_070_2
import Theorems.Thm_RH1E6S10_part_070_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_070 : RS5.BandZeros ((41868499943 : ℝ) / 65536) ((41904793624 : ℝ) / 65536) 1016 := by
  have g0 := part_070_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_070_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_070_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_070_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41868499943 : ℝ) / 65536) ((41904793624 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_070 <;> assumption

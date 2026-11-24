-- Prove2me | solution 1 for RH1E6S17.group_052
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:44:53.006688+00:00
-- url     : https://prove2.me/submissions/10b6ce28-9b5d-4005-b970-379db75a1de3

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_052_0
import Theorems.Thm_RH1E6S17_part_052_1
import Theorems.Thm_RH1E6S17_part_052_2
import Theorems.Thm_RH1E6S17_part_052_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_052 : RS5.BandZeros ((64081086317 : ℝ) / 65536) ((64116097036 : ℝ) / 65536) 1016 := by
  have g0 := part_052_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_052_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_052_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_052_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64081086317 : ℝ) / 65536) ((64116097036 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_052 <;> assumption

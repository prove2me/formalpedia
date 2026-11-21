-- Prove2me | solution 1 for RH1E6S04.group_019
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:15:34.079952+00:00
-- url     : https://prove2.me/submissions/61e25717-1c86-410f-b16c-b8469fbbedae

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_019_0
import Theorems.Thm_RH1E6S04_part_019_1
import Theorems.Thm_RH1E6S04_part_019_2
import Theorems.Thm_RH1E6S04_part_019_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_019 : RS5.BandZeros ((20397361113 : ℝ) / 65536) ((20436067169 : ℝ) / 65536) 1016 := by
  have g0 := part_019_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_019_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_019_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_019_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20397361113 : ℝ) / 65536) ((20436067169 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_019 <;> assumption

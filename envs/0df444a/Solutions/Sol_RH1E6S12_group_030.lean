-- Prove2me | solution 1 for RH1E6S12.group_030
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:06:20.971286+00:00
-- url     : https://prove2.me/submissions/f042c1eb-5493-47bb-aa9a-d7ba92e6a26d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_030_0
import Theorems.Thm_RH1E6S12_part_030_1
import Theorems.Thm_RH1E6S12_part_030_2
import Theorems.Thm_RH1E6S12_part_030_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_030 : RS5.BandZeros ((46954153625 : ℝ) / 65536) ((46990095132 : ℝ) / 65536) 1016 := by
  have g0 := part_030_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_030_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_030_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_030_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46954153625 : ℝ) / 65536) ((46990095132 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_030 <;> assumption

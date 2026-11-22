-- Prove2me | solution 1 for RH1E6S12.group_067
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T16:44:16.763018+00:00
-- url     : https://prove2.me/submissions/d85fdbdf-afd3-42b5-88a7-22912b27545a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_067_0
import Theorems.Thm_RH1E6S12_part_067_1
import Theorems.Thm_RH1E6S12_part_067_2
import Theorems.Thm_RH1E6S12_part_067_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_067 : RS5.BandZeros ((48281911340 : ℝ) / 65536) ((48317771192 : ℝ) / 65536) 1016 := by
  have g0 := part_067_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_067_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_067_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_067_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((48281911340 : ℝ) / 65536) ((48317771192 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_067 <;> assumption

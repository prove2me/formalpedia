-- Prove2me | solution 1 for RH1E6S17.group_034
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T21:51:16.234515+00:00
-- url     : https://prove2.me/submissions/a9a28ace-ce5f-4292-a1ce-033218370aee

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_034_0
import Theorems.Thm_RH1E6S17_part_034_1
import Theorems.Thm_RH1E6S17_part_034_2
import Theorems.Thm_RH1E6S17_part_034_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_034 : RS5.BandZeros ((63450928949 : ℝ) / 65536) ((63485960006 : ℝ) / 65536) 1016 := by
  have g0 := part_034_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_034_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_034_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_034_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63450928949 : ℝ) / 65536) ((63485960006 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_034 <;> assumption

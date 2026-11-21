-- Prove2me | solution 1 for RH1E6S04.group_045
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:15:16.007481+00:00
-- url     : https://prove2.me/submissions/8034183c-18ca-4de4-b6e8-c31f9e4540c9

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_045_0
import Theorems.Thm_RH1E6S04_part_045_1
import Theorems.Thm_RH1E6S04_part_045_2
import Theorems.Thm_RH1E6S04_part_045_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_045 : RS5.BandZeros ((21401300894 : ℝ) / 65536) ((21439826392 : ℝ) / 65536) 1016 := by
  have g0 := part_045_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_045_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_045_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_045_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21401300894 : ℝ) / 65536) ((21439826392 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_045 <;> assumption

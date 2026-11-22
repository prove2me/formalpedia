-- Prove2me | solution 1 for RH1E6S13.group_004
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T19:21:56.131412+00:00
-- url     : https://prove2.me/submissions/2f8288bf-ac4a-409f-a5fe-807b56d7534e

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_004_0
import Theorems.Thm_RH1E6S13_part_004_1
import Theorems.Thm_RH1E6S13_part_004_2
import Theorems.Thm_RH1E6S13_part_004_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_004 : RS5.BandZeros ((49295150009 : ℝ) / 65536) ((49330910669 : ℝ) / 65536) 1016 := by
  have g0 := part_004_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_004_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_004_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_004_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49295150009 : ℝ) / 65536) ((49330910669 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_004 <;> assumption

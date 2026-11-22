-- Prove2me | solution 1 for RH1E6S13.group_007
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T19:27:32.961165+00:00
-- url     : https://prove2.me/submissions/798fedaa-6704-48f6-acf0-e90d08567e31

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_007_0
import Theorems.Thm_RH1E6S13_part_007_1
import Theorems.Thm_RH1E6S13_part_007_2
import Theorems.Thm_RH1E6S13_part_007_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_007 : RS5.BandZeros ((49402469352 : ℝ) / 65536) ((49438240969 : ℝ) / 65536) 1016 := by
  have g0 := part_007_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_007_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_007_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_007_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49402469352 : ℝ) / 65536) ((49438240969 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_007 <;> assumption

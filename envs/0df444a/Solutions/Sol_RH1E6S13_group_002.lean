-- Prove2me | solution 1 for RH1E6S13.group_002
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T18:03:06.315613+00:00
-- url     : https://prove2.me/submissions/708e823d-e687-47b2-8825-db46de94ee57

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_002_0
import Theorems.Thm_RH1E6S13_part_002_1
import Theorems.Thm_RH1E6S13_part_002_2
import Theorems.Thm_RH1E6S13_part_002_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_002 : RS5.BandZeros ((49223586811 : ℝ) / 65536) ((49259369522 : ℝ) / 65536) 1016 := by
  have g0 := part_002_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_002_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_002_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_002_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49223586811 : ℝ) / 65536) ((49259369522 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_002 <;> assumption

-- Prove2me | solution 1 for RH1E6S13.group_018
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T21:35:30.880808+00:00
-- url     : https://prove2.me/submissions/3df103f2-fd36-4e26-8ee5-4286e6e83ff2

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_018_0
import Theorems.Thm_RH1E6S13_part_018_1
import Theorems.Thm_RH1E6S13_part_018_2
import Theorems.Thm_RH1E6S13_part_018_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_018 : RS5.BandZeros ((49795835756 : ℝ) / 65536) ((49831583141 : ℝ) / 65536) 1016 := by
  have g0 := part_018_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_018_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_018_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_018_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((49795835756 : ℝ) / 65536) ((49831583141 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_018 <;> assumption

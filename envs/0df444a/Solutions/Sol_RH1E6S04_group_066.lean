-- Prove2me | solution 1 for RH1E6S04.group_066
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:03:01.79265+00:00
-- url     : https://prove2.me/submissions/9b0c7ab5-ac0b-402f-8d2d-f72fe904bec4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_066_0
import Theorems.Thm_RH1E6S04_part_066_1
import Theorems.Thm_RH1E6S04_part_066_2
import Theorems.Thm_RH1E6S04_part_066_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_066 : RS5.BandZeros ((22209007565 : ℝ) / 65536) ((22247402209 : ℝ) / 65536) 1016 := by
  have g0 := part_066_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_066_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_066_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_066_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22209007565 : ℝ) / 65536) ((22247402209 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_066 <;> assumption

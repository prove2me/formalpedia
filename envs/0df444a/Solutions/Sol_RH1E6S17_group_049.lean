-- Prove2me | solution 1 for RH1E6S17.group_049
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:35:22.22301+00:00
-- url     : https://prove2.me/submissions/ef34eb3a-1e13-4734-853f-a481b47fdab5

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_049_0
import Theorems.Thm_RH1E6S17_part_049_1
import Theorems.Thm_RH1E6S17_part_049_2
import Theorems.Thm_RH1E6S17_part_049_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_049 : RS5.BandZeros ((63976096228 : ℝ) / 65536) ((64011094525 : ℝ) / 65536) 1016 := by
  have g0 := part_049_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_049_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_049_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_049_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63976096228 : ℝ) / 65536) ((64011094525 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_049 <;> assumption

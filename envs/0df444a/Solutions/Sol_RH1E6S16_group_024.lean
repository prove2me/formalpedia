-- Prove2me | solution 1 for RH1E6S16.group_024
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:41:44.018818+00:00
-- url     : https://prove2.me/submissions/dd09d80f-29e1-44bb-a1c3-06d784f96433

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_024_0
import Theorems.Thm_RH1E6S16_part_024_1
import Theorems.Thm_RH1E6S16_part_024_2
import Theorems.Thm_RH1E6S16_part_024_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_024 : RS5.BandZeros ((59827607585 : ℝ) / 65536) ((59862815819 : ℝ) / 65536) 1016 := by
  have g0 := part_024_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_024_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_024_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_024_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59827607585 : ℝ) / 65536) ((59862815819 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_024 <;> assumption

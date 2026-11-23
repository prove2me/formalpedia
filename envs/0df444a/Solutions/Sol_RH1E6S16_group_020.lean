-- Prove2me | solution 1 for RH1E6S16.group_020
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T15:23:33.130139+00:00
-- url     : https://prove2.me/submissions/a6672ff8-5385-4ae0-a854-191250398084

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_020_0
import Theorems.Thm_RH1E6S16_part_020_1
import Theorems.Thm_RH1E6S16_part_020_2
import Theorems.Thm_RH1E6S16_part_020_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_020 : RS5.BandZeros ((59686802921 : ℝ) / 65536) ((59722011993 : ℝ) / 65536) 1016 := by
  have g0 := part_020_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_020_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_020_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_020_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59686802921 : ℝ) / 65536) ((59722011993 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_020 <;> assumption

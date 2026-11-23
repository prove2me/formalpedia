-- Prove2me | solution 1 for RH1E6S16.group_064
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:12:11.549204+00:00
-- url     : https://prove2.me/submissions/fe5c0973-297e-4600-833a-79c1fc79da8a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_064_0
import Theorems.Thm_RH1E6S16_part_064_1
import Theorems.Thm_RH1E6S16_part_064_2
import Theorems.Thm_RH1E6S16_part_064_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_064 : RS5.BandZeros ((61234090675 : ℝ) / 65536) ((61269216924 : ℝ) / 65536) 1016 := by
  have g0 := part_064_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_064_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_064_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_064_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61234090675 : ℝ) / 65536) ((61269216924 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_064 <;> assumption

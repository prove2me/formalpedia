-- Prove2me | solution 1 for RH1E6S13.group_029
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T22:14:29.408642+00:00
-- url     : https://prove2.me/submissions/3ec7e897-ded2-4f66-ba31-7af71a294a17

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_029_0
import Theorems.Thm_RH1E6S13_part_029_1
import Theorems.Thm_RH1E6S13_part_029_2
import Theorems.Thm_RH1E6S13_part_029_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_029 : RS5.BandZeros ((50188928020 : ℝ) / 65536) ((50224660202 : ℝ) / 65536) 1016 := by
  have g0 := part_029_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_029_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_029_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_029_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50188928020 : ℝ) / 65536) ((50224660202 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_029 <;> assumption

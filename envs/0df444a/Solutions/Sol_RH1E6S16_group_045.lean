-- Prove2me | solution 1 for RH1E6S16.group_045
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T16:55:26.663704+00:00
-- url     : https://prove2.me/submissions/e4632483-7858-4732-b11c-5064481b8269

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_045_0
import Theorems.Thm_RH1E6S16_part_045_1
import Theorems.Thm_RH1E6S16_part_045_2
import Theorems.Thm_RH1E6S16_part_045_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_045 : RS5.BandZeros ((60566362897 : ℝ) / 65536) ((60601523866 : ℝ) / 65536) 1016 := by
  have g0 := part_045_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_045_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_045_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_045_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((60566362897 : ℝ) / 65536) ((60601523866 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_045 <;> assumption

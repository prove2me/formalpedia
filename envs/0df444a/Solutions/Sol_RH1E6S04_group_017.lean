-- Prove2me | solution 1 for RH1E6S04.group_017
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:13:01.734983+00:00
-- url     : https://prove2.me/submissions/4dda8e67-469e-4bea-aa11-c88c5f603c9f

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_017_0
import Theorems.Thm_RH1E6S04_part_017_1
import Theorems.Thm_RH1E6S04_part_017_2
import Theorems.Thm_RH1E6S04_part_017_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_017 : RS5.BandZeros ((20319938125 : ℝ) / 65536) ((20358648262 : ℝ) / 65536) 1016 := by
  have g0 := part_017_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_017_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_017_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_017_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20319938125 : ℝ) / 65536) ((20358648262 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_017 <;> assumption

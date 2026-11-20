-- Prove2me | solution 1 for RH1E6S00.group_068
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T23:08:47.963697+00:00
-- url     : https://prove2.me/submissions/3cce5210-65ac-4ae1-bb80-bcba60cdf7d6

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_068_0
import Theorems.Thm_RH1E6S00_part_068_1
import Theorems.Thm_RH1E6S00_part_068_2
import Theorems.Thm_RH1E6S00_part_068_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_068 : RS5.BandZeros ((9436431636 : ℝ) / 65536) ((9478093744 : ℝ) / 65536) 1016 := by
  have g0 := part_068_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_068_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_068_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_068_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((9436431636 : ℝ) / 65536) ((9478093744 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_068 <;> assumption

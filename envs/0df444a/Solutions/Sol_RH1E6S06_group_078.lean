-- Prove2me | solution 1 for RH1E6S06.group_078
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:34:47.164514+00:00
-- url     : https://prove2.me/submissions/570da6d5-0da9-47d2-a9c3-2a35d6e05812

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_078_0
import Theorems.Thm_RH1E6S06_part_078_1
import Theorems.Thm_RH1E6S06_part_078_2
import Theorems.Thm_RH1E6S06_part_078_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_078 : RS5.BandZeros ((29150184414 : ℝ) / 65536) ((29187668213 : ℝ) / 65536) 1016 := by
  have g0 := part_078_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_078_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_078_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_078_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29150184414 : ℝ) / 65536) ((29187668213 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_078 <;> assumption

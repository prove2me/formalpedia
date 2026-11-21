-- Prove2me | solution 1 for RH1E6S04.group_078
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:00:29.200175+00:00
-- url     : https://prove2.me/submissions/a2d3d432-d5e1-43de-883a-cefdca2aa64a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_078_0
import Theorems.Thm_RH1E6S04_part_078_1
import Theorems.Thm_RH1E6S04_part_078_2
import Theorems.Thm_RH1E6S04_part_078_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_078 : RS5.BandZeros ((22669344943 : ℝ) / 65536) ((22707676930 : ℝ) / 65536) 1016 := by
  have g0 := part_078_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_078_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_078_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_078_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22669344943 : ℝ) / 65536) ((22707676930 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_078 <;> assumption

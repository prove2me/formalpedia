-- Prove2me | solution 1 for RH1E6S09.group_005
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:36:33.039972+00:00
-- url     : https://prove2.me/submissions/5e213fe8-01c3-4a8b-ab44-71fd91772d00

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_005_0
import Theorems.Thm_RH1E6S09_part_005_1
import Theorems.Thm_RH1E6S09_part_005_2
import Theorems.Thm_RH1E6S09_part_005_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_005 : RS5.BandZeros ((36228562649 : ℝ) / 65536) ((36265298183 : ℝ) / 65536) 1016 := by
  have g0 := part_005_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_005_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_005_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_005_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36228562649 : ℝ) / 65536) ((36265298183 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_005 <;> assumption

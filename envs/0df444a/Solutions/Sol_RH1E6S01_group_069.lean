-- Prove2me | solution 1 for RH1E6S01.group_069
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:53:44.235478+00:00
-- url     : https://prove2.me/submissions/400b9d5c-5b70-488f-96d7-24efe299ca3f

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_069_0
import Theorems.Thm_RH1E6S01_part_069_1
import Theorems.Thm_RH1E6S01_part_069_2
import Theorems.Thm_RH1E6S01_part_069_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_069 : RS5.BandZeros ((12657116235 : ℝ) / 65536) ((12697607013 : ℝ) / 65536) 1016 := by
  have g0 := part_069_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_069_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_069_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_069_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12657116235 : ℝ) / 65536) ((12697607013 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_069 <;> assumption

-- Prove2me | solution 1 for RH1E6S15.group_055
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T11:28:01.986457+00:00
-- url     : https://prove2.me/submissions/e8769a0d-6937-48a0-ac51-e7d79ca07f68

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_055_0
import Theorems.Thm_RH1E6S15_part_055_1
import Theorems.Thm_RH1E6S15_part_055_2
import Theorems.Thm_RH1E6S15_part_055_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_055 : RS5.BandZeros ((57650221345 : ℝ) / 65536) ((57685541258 : ℝ) / 65536) 1016 := by
  have g0 := part_055_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_055_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_055_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_055_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57650221345 : ℝ) / 65536) ((57685541258 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_055 <;> assumption

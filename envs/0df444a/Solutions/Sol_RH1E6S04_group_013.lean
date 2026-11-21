-- Prove2me | solution 1 for RH1E6S04.group_013
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:00:35.907955+00:00
-- url     : https://prove2.me/submissions/47f7d64b-5d50-4507-a08d-75c7fc9cedf8

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_013_0
import Theorems.Thm_RH1E6S04_part_013_1
import Theorems.Thm_RH1E6S04_part_013_2
import Theorems.Thm_RH1E6S04_part_013_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_013 : RS5.BandZeros ((20165048222 : ℝ) / 65536) ((20203776226 : ℝ) / 65536) 1016 := by
  have g0 := part_013_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_013_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_013_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_013_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20165048222 : ℝ) / 65536) ((20203776226 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_013 <;> assumption

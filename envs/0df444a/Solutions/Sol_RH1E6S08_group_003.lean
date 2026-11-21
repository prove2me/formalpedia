-- Prove2me | solution 1 for RH1E6S08.group_003
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:17:24.24012+00:00
-- url     : https://prove2.me/submissions/a6abded4-5663-48aa-bccb-cdc1285d67f5

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_003_0
import Theorems.Thm_RH1E6S08_part_003_1
import Theorems.Thm_RH1E6S08_part_003_2
import Theorems.Thm_RH1E6S08_part_003_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_003 : RS5.BandZeros ((32879238972 : ℝ) / 65536) ((32916294185 : ℝ) / 65536) 1016 := by
  have g0 := part_003_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_003_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_003_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_003_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((32879238972 : ℝ) / 65536) ((32916294185 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_003 <;> assumption

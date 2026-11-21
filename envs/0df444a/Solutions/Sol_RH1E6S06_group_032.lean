-- Prove2me | solution 1 for RH1E6S06.group_032
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:43:38.32024+00:00
-- url     : https://prove2.me/submissions/ddbda840-c4a2-4d17-ba18-be6eb6348b82

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_032_0
import Theorems.Thm_RH1E6S06_part_032_1
import Theorems.Thm_RH1E6S06_part_032_2
import Theorems.Thm_RH1E6S06_part_032_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_032 : RS5.BandZeros ((27422244344 : ℝ) / 65536) ((27459886807 : ℝ) / 65536) 1016 := by
  have g0 := part_032_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_032_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_032_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_032_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27422244344 : ℝ) / 65536) ((27459886807 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_032 <;> assumption

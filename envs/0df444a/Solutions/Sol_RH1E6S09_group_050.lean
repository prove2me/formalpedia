-- Prove2me | solution 1 for RH1E6S09.group_050
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:45:01.968253+00:00
-- url     : https://prove2.me/submissions/b580bf97-45f8-4d53-90f4-d27ea51fa886

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_050_0
import Theorems.Thm_RH1E6S09_part_050_1
import Theorems.Thm_RH1E6S09_part_050_2
import Theorems.Thm_RH1E6S09_part_050_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_050 : RS5.BandZeros ((37878943381 : ℝ) / 65536) ((37915536492 : ℝ) / 65536) 1016 := by
  have g0 := part_050_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_050_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_050_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_050_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37878943381 : ℝ) / 65536) ((37915536492 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_050 <;> assumption

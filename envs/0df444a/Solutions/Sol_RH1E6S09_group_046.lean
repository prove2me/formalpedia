-- Prove2me | solution 1 for RH1E6S09.group_046
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:28:46.89118+00:00
-- url     : https://prove2.me/submissions/a6a3b29b-0d54-4b4e-b8fe-9f25ad61cf21

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_046_0
import Theorems.Thm_RH1E6S09_part_046_1
import Theorems.Thm_RH1E6S09_part_046_2
import Theorems.Thm_RH1E6S09_part_046_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_046 : RS5.BandZeros ((37732484666 : ℝ) / 65536) ((37769106182 : ℝ) / 65536) 1016 := by
  have g0 := part_046_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_046_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_046_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_046_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37732484666 : ℝ) / 65536) ((37769106182 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_046 <;> assumption

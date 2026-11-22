-- Prove2me | solution 1 for RH1E6S09.group_052
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T10:47:47.510487+00:00
-- url     : https://prove2.me/submissions/7a6a2d30-d56d-43e6-8562-7437104373d2

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_052_0
import Theorems.Thm_RH1E6S09_part_052_1
import Theorems.Thm_RH1E6S09_part_052_2
import Theorems.Thm_RH1E6S09_part_052_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_052 : RS5.BandZeros ((37952139399 : ℝ) / 65536) ((37988735709 : ℝ) / 65536) 1016 := by
  have g0 := part_052_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_052_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_052_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_052_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((37952139399 : ℝ) / 65536) ((37988735709 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_052 <;> assumption

-- Prove2me | solution 1 for RH1E6S13.group_074
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T01:33:15.936897+00:00
-- url     : https://prove2.me/submissions/b2a02652-a8bc-42f4-ae51-4312a1ee1822

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_074_0
import Theorems.Thm_RH1E6S13_part_074_1
import Theorems.Thm_RH1E6S13_part_074_2
import Theorems.Thm_RH1E6S13_part_074_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_074 : RS5.BandZeros ((51794377484 : ℝ) / 65536) ((51830005123 : ℝ) / 65536) 1016 := by
  have g0 := part_074_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_074_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_074_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_074_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51794377484 : ℝ) / 65536) ((51830005123 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_074 <;> assumption

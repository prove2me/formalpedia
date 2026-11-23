-- Prove2me | solution 1 for RH1E6S15.group_043
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:41:24.724608+00:00
-- url     : https://prove2.me/submissions/55ac8921-6cdf-41b5-a339-72174cbfcf94

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_043_0
import Theorems.Thm_RH1E6S15_part_043_1
import Theorems.Thm_RH1E6S15_part_043_2
import Theorems.Thm_RH1E6S15_part_043_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_043 : RS5.BandZeros ((57226414259 : ℝ) / 65536) ((57261737379 : ℝ) / 65536) 1016 := by
  have g0 := part_043_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_043_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_043_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_043_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57226414259 : ℝ) / 65536) ((57261737379 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_043 <;> assumption

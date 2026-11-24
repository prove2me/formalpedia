-- Prove2me | solution 1 for RH1E6S17.group_042
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T22:13:14.796512+00:00
-- url     : https://prove2.me/submissions/48c2f8d1-ceb2-4370-8c1a-37303df85533

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_042_0
import Theorems.Thm_RH1E6S17_part_042_1
import Theorems.Thm_RH1E6S17_part_042_2
import Theorems.Thm_RH1E6S17_part_042_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_042 : RS5.BandZeros ((63731071855 : ℝ) / 65536) ((63766090001 : ℝ) / 65536) 1016 := by
  have g0 := part_042_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_042_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_042_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_042_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((63731071855 : ℝ) / 65536) ((63766090001 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_042 <;> assumption

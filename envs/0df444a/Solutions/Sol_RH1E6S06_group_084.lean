-- Prove2me | solution 1 for RH1E6S06.group_084
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:53:50.617849+00:00
-- url     : https://prove2.me/submissions/c7a65a47-ab09-41cb-8ef9-e009a0cfc070

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_084_0
import Theorems.Thm_RH1E6S06_part_084_1
import Theorems.Thm_RH1E6S06_part_084_2
import Theorems.Thm_RH1E6S06_part_084_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_084 : RS5.BandZeros ((29374896224 : ℝ) / 65536) ((29412327669 : ℝ) / 65536) 1016 := by
  have g0 := part_084_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_084_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_084_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_084_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29374896224 : ℝ) / 65536) ((29412327669 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_084 <;> assumption

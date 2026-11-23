-- Prove2me | solution 1 for RH1E6S14.group_078
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:13:44.126803+00:00
-- url     : https://prove2.me/submissions/015dc41e-c929-42b6-a059-a8ce356c238d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_078_0
import Theorems.Thm_RH1E6S14_part_078_1
import Theorems.Thm_RH1E6S14_part_078_2
import Theorems.Thm_RH1E6S14_part_078_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_078 : RS5.BandZeros ((55198855576 : ℝ) / 65536) ((55234260218 : ℝ) / 65536) 1016 := by
  have g0 := part_078_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_078_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_078_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_078_3
  exact g3
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55198855576 : ℝ) / 65536) ((55234260218 : ℝ) / 65536) 1016 := by
  apply RH1E6S14.group_078 <;> assumption

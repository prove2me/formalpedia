-- Prove2me | solution 1 for RH1E6S11.group_070
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:32:46.505385+00:00
-- url     : https://prove2.me/submissions/d552695f-ac03-432b-b91e-4fc699101ea9

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_070_0
import Theorems.Thm_RH1E6S11_part_070_1
import Theorems.Thm_RH1E6S11_part_070_2
import Theorems.Thm_RH1E6S11_part_070_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_070 : RS5.BandZeros ((45128242497 : ℝ) / 65536) ((45164284065 : ℝ) / 65536) 1016 := by
  have g0 := part_070_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_070_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_070_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_070_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45128242497 : ℝ) / 65536) ((45164284065 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_070 <;> assumption

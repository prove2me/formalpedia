-- Prove2me | solution 1 for RH1E6S07.group_068
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:18:51.120768+00:00
-- url     : https://prove2.me/submissions/9f6a8146-e536-4c86-a782-ddf121a332b5

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S07_part_068_0
import Theorems.Thm_RH1E6S07_part_068_1
import Theorems.Thm_RH1E6S07_part_068_2
import Theorems.Thm_RH1E6S07_part_068_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem group_068 : RS5.BandZeros ((32026513632 : ℝ) / 65536) ((32063675798 : ℝ) / 65536) 1016 := by
  have g0 := part_068_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_068_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_068_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_068_3
  exact g3
end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32026513632 : ℝ) / 65536) ((32063675798 : ℝ) / 65536) 1016 := by
  apply RH1E6S07.group_068 <;> assumption

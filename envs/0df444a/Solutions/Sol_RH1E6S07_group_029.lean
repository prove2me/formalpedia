-- Prove2me | solution 1 for RH1E6S07.group_029
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:30:34.386182+00:00
-- url     : https://prove2.me/submissions/5238c419-a1c9-4550-8e0a-1af84e26fade

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S07_part_029_0
import Theorems.Thm_RH1E6S07_part_029_1
import Theorems.Thm_RH1E6S07_part_029_2
import Theorems.Thm_RH1E6S07_part_029_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem group_029 : RS5.BandZeros ((30574724068 : ℝ) / 65536) ((30612015379 : ℝ) / 65536) 1016 := by
  have g0 := part_029_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_029_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_029_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_029_3
  exact g3
end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30574724068 : ℝ) / 65536) ((30612015379 : ℝ) / 65536) 1016 := by
  apply RH1E6S07.group_029 <;> assumption

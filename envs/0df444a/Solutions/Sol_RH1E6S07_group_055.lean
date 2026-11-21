-- Prove2me | solution 1 for RH1E6S07.group_055
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:42:25.35574+00:00
-- url     : https://prove2.me/submissions/0da273af-203d-4c2b-8d96-b78a78c52e03

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S07_part_055_0
import Theorems.Thm_RH1E6S07_part_055_1
import Theorems.Thm_RH1E6S07_part_055_2
import Theorems.Thm_RH1E6S07_part_055_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem group_055 : RS5.BandZeros ((31543269827 : ℝ) / 65536) ((31580441882 : ℝ) / 65536) 1016 := by
  have g0 := part_055_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_055_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_055_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_055_3
  exact g3
end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31543269827 : ℝ) / 65536) ((31580441882 : ℝ) / 65536) 1016 := by
  apply RH1E6S07.group_055 <;> assumption

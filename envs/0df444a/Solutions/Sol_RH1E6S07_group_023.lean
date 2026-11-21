-- Prove2me | solution 1 for RH1E6S07.group_023
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T00:11:27.383971+00:00
-- url     : https://prove2.me/submissions/ed1c92de-bc72-48e4-a6c0-5ce50fdded8f

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S07_part_023_0
import Theorems.Thm_RH1E6S07_part_023_1
import Theorems.Thm_RH1E6S07_part_023_2
import Theorems.Thm_RH1E6S07_part_023_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem group_023 : RS5.BandZeros ((30350824852 : ℝ) / 65536) ((30388159423 : ℝ) / 65536) 1016 := by
  have g0 := part_023_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_023_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_023_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_023_3
  exact g3
end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((30350824852 : ℝ) / 65536) ((30388159423 : ℝ) / 65536) 1016 := by
  apply RH1E6S07.group_023 <;> assumption

-- Prove2me | solution 1 for RH1E6S07.group_012
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T23:37:34.1705+00:00
-- url     : https://prove2.me/submissions/8e4acde8-0be4-4a0c-9c30-6ab06a767093

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S07_part_012_0
import Theorems.Thm_RH1E6S07_part_012_1
import Theorems.Thm_RH1E6S07_part_012_2
import Theorems.Thm_RH1E6S07_part_012_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem group_012 : RS5.BandZeros ((29939974749 : ℝ) / 65536) ((29977356973 : ℝ) / 65536) 1016 := by
  have g0 := part_012_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_012_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_012_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_012_3
  exact g3
end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((29939974749 : ℝ) / 65536) ((29977356973 : ℝ) / 65536) 1016 := by
  apply RH1E6S07.group_012 <;> assumption

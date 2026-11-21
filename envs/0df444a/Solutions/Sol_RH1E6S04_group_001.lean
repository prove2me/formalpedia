-- Prove2me | solution 1 for RH1E6S04.group_001
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:33:22.889583+00:00
-- url     : https://prove2.me/submissions/28c8ad40-3338-4a99-b89f-442ce7476f03

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_001_0
import Theorems.Thm_RH1E6S04_part_001_1
import Theorems.Thm_RH1E6S04_part_001_2
import Theorems.Thm_RH1E6S04_part_001_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_001 : RS5.BandZeros ((19699626644 : ℝ) / 65536) ((19738476683 : ℝ) / 65536) 1016 := by
  have g0 := part_001_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_001_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_001_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_001_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((19699626644 : ℝ) / 65536) ((19738476683 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_001 <;> assumption

-- Prove2me | solution 1 for RH1E6S04.group_074
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T11:49:39.724045+00:00
-- url     : https://prove2.me/submissions/5d20658e-e688-413a-ac52-70e74f96b084

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_074_0
import Theorems.Thm_RH1E6S04_part_074_1
import Theorems.Thm_RH1E6S04_part_074_2
import Theorems.Thm_RH1E6S04_part_074_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_074 : RS5.BandZeros ((22516004664 : ℝ) / 65536) ((22554360475 : ℝ) / 65536) 1016 := by
  have g0 := part_074_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_074_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_074_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_074_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22516004664 : ℝ) / 65536) ((22554360475 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_074 <;> assumption

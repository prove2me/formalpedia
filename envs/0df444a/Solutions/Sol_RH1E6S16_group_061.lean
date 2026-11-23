-- Prove2me | solution 1 for RH1E6S16.group_061
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T18:02:58.389991+00:00
-- url     : https://prove2.me/submissions/6c5d433a-0b0c-4470-b441-169d0ce73b04

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_061_0
import Theorems.Thm_RH1E6S16_part_061_1
import Theorems.Thm_RH1E6S16_part_061_2
import Theorems.Thm_RH1E6S16_part_061_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_061 : RS5.BandZeros ((61128683026 : ℝ) / 65536) ((61163843758 : ℝ) / 65536) 1016 := by
  have g0 := part_061_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_061_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_061_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_061_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((61128683026 : ℝ) / 65536) ((61163843758 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_061 <;> assumption

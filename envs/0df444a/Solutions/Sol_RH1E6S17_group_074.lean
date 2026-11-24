-- Prove2me | solution 1 for RH1E6S17.group_074
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T23:59:03.177884+00:00
-- url     : https://prove2.me/submissions/ab53c371-e105-4ab3-b050-98f92b8306d5

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_074_0
import Theorems.Thm_RH1E6S17_part_074_1
import Theorems.Thm_RH1E6S17_part_074_2
import Theorems.Thm_RH1E6S17_part_074_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_074 : RS5.BandZeros ((64850584545 : ℝ) / 65536) ((64885543150 : ℝ) / 65536) 1016 := by
  have g0 := part_074_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_074_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_074_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_074_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((64850584545 : ℝ) / 65536) ((64885543150 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_074 <;> assumption

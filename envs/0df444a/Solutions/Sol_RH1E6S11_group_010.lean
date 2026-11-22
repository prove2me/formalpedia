-- Prove2me | solution 1 for RH1E6S11.group_010
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:43:02.130595+00:00
-- url     : https://prove2.me/submissions/ec2e56b5-ad57-40dc-ba52-bcd721cb3649

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_010_0
import Theorems.Thm_RH1E6S11_part_010_1
import Theorems.Thm_RH1E6S11_part_010_2
import Theorems.Thm_RH1E6S11_part_010_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_010 : RS5.BandZeros ((42960590882 : ℝ) / 65536) ((42996794819 : ℝ) / 65536) 1016 := by
  have g0 := part_010_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_010_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_010_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_010_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((42960590882 : ℝ) / 65536) ((42996794819 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_010 <;> assumption

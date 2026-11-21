-- Prove2me | solution 1 for RH1E6S06.group_066
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T21:39:05.977925+00:00
-- url     : https://prove2.me/submissions/391db110-3b13-4948-a51d-f2ac9df76753

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_066_0
import Theorems.Thm_RH1E6S06_part_066_1
import Theorems.Thm_RH1E6S06_part_066_2
import Theorems.Thm_RH1E6S06_part_066_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_066 : RS5.BandZeros ((28700332443 : ℝ) / 65536) ((28737834966 : ℝ) / 65536) 1016 := by
  have g0 := part_066_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_066_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_066_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_066_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28700332443 : ℝ) / 65536) ((28737834966 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_066 <;> assumption

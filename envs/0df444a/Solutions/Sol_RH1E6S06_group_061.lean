-- Prove2me | solution 1 for RH1E6S06.group_061
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T20:59:39.534877+00:00
-- url     : https://prove2.me/submissions/ca97e9a8-8329-479d-9f25-465969dc641c

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_061_0
import Theorems.Thm_RH1E6S06_part_061_1
import Theorems.Thm_RH1E6S06_part_061_2
import Theorems.Thm_RH1E6S06_part_061_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_061 : RS5.BandZeros ((28512691786 : ℝ) / 65536) ((28550228168 : ℝ) / 65536) 1016 := by
  have g0 := part_061_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_061_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_061_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_061_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((28512691786 : ℝ) / 65536) ((28550228168 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_061 <;> assumption

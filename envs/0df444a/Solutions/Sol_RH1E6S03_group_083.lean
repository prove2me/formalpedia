-- Prove2me | solution 1 for RH1E6S03.group_083
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:28:29.796273+00:00
-- url     : https://prove2.me/submissions/1076721d-44a0-49ea-aba9-da57bfb25765

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_083_0
import Theorems.Thm_RH1E6S03_part_083_1
import Theorems.Thm_RH1E6S03_part_083_2
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_083 : RS5.BandZeros ((19633946547 : ℝ) / 65536) ((19660800000 : ℝ) / 65536) 703 := by
  have g0 := part_083_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_083_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_083_2
  exact g2
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19633946547 : ℝ) / 65536) ((19660800000 : ℝ) / 65536) 703 := by
  apply RH1E6S03.group_083 <;> assumption

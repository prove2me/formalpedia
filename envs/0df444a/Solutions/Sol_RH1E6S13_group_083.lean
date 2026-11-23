-- Prove2me | solution 1 for RH1E6S13.group_083
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:07:46.575809+00:00
-- url     : https://prove2.me/submissions/2901b5d7-fd80-44ec-b659-43d79b6988fb

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_083_0
import Theorems.Thm_RH1E6S13_part_083_1
import Theorems.Thm_RH1E6S13_part_083_2
import Theorems.Thm_RH1E6S13_part_083_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_083 : RS5.BandZeros ((52114942550 : ℝ) / 65536) ((52150551486 : ℝ) / 65536) 1016 := by
  have g0 := part_083_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_083_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_083_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_083_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52114942550 : ℝ) / 65536) ((52150551486 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_083 <;> assumption

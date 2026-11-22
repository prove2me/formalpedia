-- Prove2me | solution 1 for RH1E6S10.group_089
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:09:25.297521+00:00
-- url     : https://prove2.me/submissions/96d30af1-e9ae-4b98-b206-d4aa8fcd12bb

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_089_0
import Theorems.Thm_RH1E6S10_part_089_1
import Theorems.Thm_RH1E6S10_part_089_2
import Theorems.Thm_RH1E6S10_part_089_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_089 : RS5.BandZeros ((42557456106 : ℝ) / 65536) ((42593680676 : ℝ) / 65536) 1016 := by
  have g0 := part_089_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_089_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_089_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_089_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42557456106 : ℝ) / 65536) ((42593680676 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_089 <;> assumption

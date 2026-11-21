-- Prove2me | solution 1 for RH1E6S05.group_072
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T17:12:27.828283+00:00
-- url     : https://prove2.me/submissions/6dcc2121-a397-4d9d-9c7c-bdfb44652340

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_072_0
import Theorems.Thm_RH1E6S05_part_072_1
import Theorems.Thm_RH1E6S05_part_072_2
import Theorems.Thm_RH1E6S05_part_072_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_072 : RS5.BandZeros ((25679625392 : ℝ) / 65536) ((25717524893 : ℝ) / 65536) 1016 := by
  have g0 := part_072_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_072_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_072_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_072_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25679625392 : ℝ) / 65536) ((25717524893 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_072 <;> assumption

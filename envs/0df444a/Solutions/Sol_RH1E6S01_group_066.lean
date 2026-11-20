-- Prove2me | solution 1 for RH1E6S01.group_066
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:46:30.603375+00:00
-- url     : https://prove2.me/submissions/20ddaf76-dddd-487f-989b-508b6dfa9785

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_066_0
import Theorems.Thm_RH1E6S01_part_066_1
import Theorems.Thm_RH1E6S01_part_066_2
import Theorems.Thm_RH1E6S01_part_066_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_066 : RS5.BandZeros ((12535598371 : ℝ) / 65536) ((12576116945 : ℝ) / 65536) 1016 := by
  have g0 := part_066_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_066_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_066_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_066_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((12535598371 : ℝ) / 65536) ((12576116945 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_066 <;> assumption

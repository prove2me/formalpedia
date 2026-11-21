-- Prove2me | solution 1 for RH1E6S03.group_072
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T08:03:40.37131+00:00
-- url     : https://prove2.me/submissions/0a1a0d51-12bd-496f-b805-5f3ecfecd2b4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_072_0
import Theorems.Thm_RH1E6S03_part_072_1
import Theorems.Thm_RH1E6S03_part_072_2
import Theorems.Thm_RH1E6S03_part_072_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_072 : RS5.BandZeros ((19206304400 : ℝ) / 65536) ((19245198111 : ℝ) / 65536) 1016 := by
  have g0 := part_072_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_072_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_072_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_072_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((19206304400 : ℝ) / 65536) ((19245198111 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_072 <;> assumption

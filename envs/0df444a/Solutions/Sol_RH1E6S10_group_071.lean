-- Prove2me | solution 1 for RH1E6S10.group_071
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:21:25.794804+00:00
-- url     : https://prove2.me/submissions/84af7675-4c84-484e-bb89-ea64b5cb9574

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_071_0
import Theorems.Thm_RH1E6S10_part_071_1
import Theorems.Thm_RH1E6S10_part_071_2
import Theorems.Thm_RH1E6S10_part_071_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_071 : RS5.BandZeros ((41904793624 : ℝ) / 65536) ((41941084578 : ℝ) / 65536) 1016 := by
  have g0 := part_071_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_071_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_071_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_071_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((41904793624 : ℝ) / 65536) ((41941084578 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_071 <;> assumption

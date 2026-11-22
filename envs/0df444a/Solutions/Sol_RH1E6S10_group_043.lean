-- Prove2me | solution 1 for RH1E6S10.group_043
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T01:02:58.570175+00:00
-- url     : https://prove2.me/submissions/4fca0171-e723-42fb-a3c8-5d4c4bf29cec

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_043_0
import Theorems.Thm_RH1E6S10_part_043_1
import Theorems.Thm_RH1E6S10_part_043_2
import Theorems.Thm_RH1E6S10_part_043_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_043 : RS5.BandZeros ((40887788583 : ℝ) / 65536) ((40924148044 : ℝ) / 65536) 1016 := by
  have g0 := part_043_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_043_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_043_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_043_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40887788583 : ℝ) / 65536) ((40924148044 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_043 <;> assumption

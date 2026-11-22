-- Prove2me | solution 1 for RH1E6S10.group_084
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:55:20.309819+00:00
-- url     : https://prove2.me/submissions/2c83e029-f67b-484c-8f31-d6f8c9135c79

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_084_0
import Theorems.Thm_RH1E6S10_part_084_1
import Theorems.Thm_RH1E6S10_part_084_2
import Theorems.Thm_RH1E6S10_part_084_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_084 : RS5.BandZeros ((42376248535 : ℝ) / 65536) ((42412495411 : ℝ) / 65536) 1016 := by
  have g0 := part_084_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_084_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_084_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_084_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42376248535 : ℝ) / 65536) ((42412495411 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_084 <;> assumption

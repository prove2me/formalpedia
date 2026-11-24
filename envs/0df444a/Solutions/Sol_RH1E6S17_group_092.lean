-- Prove2me | solution 1 for RH1E6S17.group_092
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:56:49.041011+00:00
-- url     : https://prove2.me/submissions/74ec0081-e740-4029-9281-b5b2c34e6550

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_092_0
import Theorems.Thm_RH1E6S17_part_092_1
import Theorems.Thm_RH1E6S17_part_092_2
import Theorems.Thm_RH1E6S17_part_092_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_092 : RS5.BandZeros ((65479582316 : ℝ) / 65536) ((65514529945 : ℝ) / 65536) 1016 := by
  have g0 := part_092_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_092_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_092_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_092_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65479582316 : ℝ) / 65536) ((65514529945 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_092 <;> assumption

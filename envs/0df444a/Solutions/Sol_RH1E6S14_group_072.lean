-- Prove2me | solution 1 for RH1E6S14.group_072
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T06:55:52.724699+00:00
-- url     : https://prove2.me/submissions/a34c216e-3b33-4145-8a4e-977878b20910

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_072_0
import Theorems.Thm_RH1E6S14_part_072_1
import Theorems.Thm_RH1E6S14_part_072_2
import Theorems.Thm_RH1E6S14_part_072_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_072 : RS5.BandZeros ((54986191353 : ℝ) / 65536) ((55021631191 : ℝ) / 65536) 1016 := by
  have g0 := part_072_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_072_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_072_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_072_3
  exact g3
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((54986191353 : ℝ) / 65536) ((55021631191 : ℝ) / 65536) 1016 := by
  apply RH1E6S14.group_072 <;> assumption

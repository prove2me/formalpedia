-- Prove2me | solution 1 for RH1E6S14.group_092
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T07:52:52.38693+00:00
-- url     : https://prove2.me/submissions/cdd94233-d7c5-490f-8ac9-ece79c411e44

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_092_0
import Theorems.Thm_RH1E6S14_part_092_1
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_092 : RS5.BandZeros ((55694770625 : ℝ) / 65536) ((55705600000 : ℝ) / 65536) 310 := by
  have g0 := part_092_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_092_1
  exact g1
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((55694770625 : ℝ) / 65536) ((55705600000 : ℝ) / 65536) 310 := by
  apply RH1E6S14.group_092 <;> assumption

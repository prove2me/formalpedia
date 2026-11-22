-- Prove2me | solution 1 for RH1E6S09.group_089
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T16:54:29.408196+00:00
-- url     : https://prove2.me/submissions/e27343da-5564-4818-9dca-eb6f44c8bec9

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_089_0
import Theorems.Thm_RH1E6S09_part_089_1
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_089 : RS5.BandZeros ((39304174719 : ℝ) / 65536) ((39321600000 : ℝ) / 65536) 486 := by
  have g0 := part_089_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_089_1
  exact g1
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((39304174719 : ℝ) / 65536) ((39321600000 : ℝ) / 65536) 486 := by
  apply RH1E6S09.group_089 <;> assumption

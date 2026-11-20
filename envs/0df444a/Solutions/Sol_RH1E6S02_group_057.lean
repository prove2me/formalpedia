-- Prove2me | solution 1 for RH1E6S02.group_057
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T04:15:49.881952+00:00
-- url     : https://prove2.me/submissions/0e16efca-e8a5-44b3-8dc8-62d3e90c5491

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S02_part_057_0
import Theorems.Thm_RH1E6S02_part_057_1
import Theorems.Thm_RH1E6S02_part_057_2
import Theorems.Thm_RH1E6S02_part_057_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem group_057 : RS5.BandZeros ((15389051514 : ℝ) / 65536) ((15428786863 : ℝ) / 65536) 1016 := by
  have g0 := part_057_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_057_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_057_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_057_3
  exact g3
end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((15389051514 : ℝ) / 65536) ((15428786863 : ℝ) / 65536) 1016 := by
  apply RH1E6S02.group_057 <;> assumption

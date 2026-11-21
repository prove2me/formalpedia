-- Prove2me | solution 1 for RH1E6S07.group_047
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T01:19:10.807319+00:00
-- url     : https://prove2.me/submissions/6d525763-c437-41e9-93d4-d5d833826d36

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S07_part_047_0
import Theorems.Thm_RH1E6S07_part_047_1
import Theorems.Thm_RH1E6S07_part_047_2
import Theorems.Thm_RH1E6S07_part_047_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem group_047 : RS5.BandZeros ((31245525946 : ℝ) / 65536) ((31282752145 : ℝ) / 65536) 1016 := by
  have g0 := part_047_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_047_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_047_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_047_3
  exact g3
end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((31245525946 : ℝ) / 65536) ((31282752145 : ℝ) / 65536) 1016 := by
  apply RH1E6S07.group_047 <;> assumption

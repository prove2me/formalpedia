-- Prove2me | solution 1 for RH1E6S00.group_040
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:14:57.759729+00:00
-- url     : https://prove2.me/submissions/b12aea89-70f2-441a-95e7-2b07c08df84b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_040_0
import Theorems.Thm_RH1E6S00_part_040_1
import Theorems.Thm_RH1E6S00_part_040_2
import Theorems.Thm_RH1E6S00_part_040_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_040 : RS5.BandZeros ((8262035137 : ℝ) / 65536) ((8304254578 : ℝ) / 65536) 1016 := by
  have g0 := part_040_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_040_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_040_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_040_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8262035137 : ℝ) / 65536) ((8304254578 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_040 <;> assumption

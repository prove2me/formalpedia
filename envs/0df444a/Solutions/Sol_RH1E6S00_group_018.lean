-- Prove2me | solution 1 for RH1E6S00.group_018
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:30:40.334039+00:00
-- url     : https://prove2.me/submissions/f5fe8258-a9e0-49b4-a6df-436afc011b22

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_018_0
import Theorems.Thm_RH1E6S00_part_018_1
import Theorems.Thm_RH1E6S00_part_018_2
import Theorems.Thm_RH1E6S00_part_018_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_018 : RS5.BandZeros ((7327418804 : ℝ) / 65536) ((7370154423 : ℝ) / 65536) 1016 := by
  have g0 := part_018_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_018_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_018_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_018_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7327418804 : ℝ) / 65536) ((7370154423 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_018 <;> assumption

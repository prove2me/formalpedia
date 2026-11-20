-- Prove2me | solution 1 for RH1E6S00.group_049
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:33:38.872375+00:00
-- url     : https://prove2.me/submissions/fb1d71fa-2a6c-4241-a65c-81fa8c961833

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_049_0
import Theorems.Thm_RH1E6S00_part_049_1
import Theorems.Thm_RH1E6S00_part_049_2
import Theorems.Thm_RH1E6S00_part_049_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_049 : RS5.BandZeros ((8641221958 : ℝ) / 65536) ((8683261932 : ℝ) / 65536) 1016 := by
  have g0 := part_049_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_049_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_049_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_049_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8641221958 : ℝ) / 65536) ((8683261932 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_049 <;> assumption

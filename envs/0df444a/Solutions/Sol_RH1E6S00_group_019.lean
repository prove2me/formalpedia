-- Prove2me | solution 1 for RH1E6S00.group_019
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:35:27.537465+00:00
-- url     : https://prove2.me/submissions/1d083ac4-6e5c-492c-a10f-5f0df45d401a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_019_0
import Theorems.Thm_RH1E6S00_part_019_1
import Theorems.Thm_RH1E6S00_part_019_2
import Theorems.Thm_RH1E6S00_part_019_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_019 : RS5.BandZeros ((7370154423 : ℝ) / 65536) ((7412864751 : ℝ) / 65536) 1016 := by
  have g0 := part_019_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_019_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_019_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_019_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7370154423 : ℝ) / 65536) ((7412864751 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_019 <;> assumption

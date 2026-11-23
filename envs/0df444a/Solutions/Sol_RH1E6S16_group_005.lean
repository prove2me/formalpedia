-- Prove2me | solution 1 for RH1E6S16.group_005
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T14:26:34.429835+00:00
-- url     : https://prove2.me/submissions/cd52ccac-6594-440d-a6e0-b681b2cda2bb

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S16_part_005_0
import Theorems.Thm_RH1E6S16_part_005_1
import Theorems.Thm_RH1E6S16_part_005_2
import Theorems.Thm_RH1E6S16_part_005_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S16

theorem group_005 : RS5.BandZeros ((59158556892 : ℝ) / 65536) ((59193793796 : ℝ) / 65536) 1016 := by
  have g0 := part_005_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_005_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_005_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_005_3
  exact g3
end RH1E6S16
open RH1E6S16 in
theorem solution : RS5.BandZeros ((59158556892 : ℝ) / 65536) ((59193793796 : ℝ) / 65536) 1016 := by
  apply RH1E6S16.group_005 <;> assumption

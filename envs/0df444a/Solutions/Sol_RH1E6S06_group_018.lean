-- Prove2me | solution 1 for RH1E6S06.group_018
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T18:09:03.19489+00:00
-- url     : https://prove2.me/submissions/3d2a42b0-8df4-43be-9ef0-5d8e3e6bc60f

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_018_0
import Theorems.Thm_RH1E6S06_part_018_1
import Theorems.Thm_RH1E6S06_part_018_2
import Theorems.Thm_RH1E6S06_part_018_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_018 : RS5.BandZeros ((26894403617 : ℝ) / 65536) ((26932154537 : ℝ) / 65536) 1016 := by
  have g0 := part_018_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_018_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_018_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_018_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((26894403617 : ℝ) / 65536) ((26932154537 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_018 <;> assumption

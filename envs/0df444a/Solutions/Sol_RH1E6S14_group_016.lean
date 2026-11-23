-- Prove2me | solution 1 for RH1E6S14.group_016
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T03:49:54.440312+00:00
-- url     : https://prove2.me/submissions/8e1b798a-8828-493b-ac3a-a5097c8c9d07

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_016_0
import Theorems.Thm_RH1E6S14_part_016_1
import Theorems.Thm_RH1E6S14_part_016_2
import Theorems.Thm_RH1E6S14_part_016_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_016 : RS5.BandZeros ((52998007421 : ℝ) / 65536) ((53033567098 : ℝ) / 65536) 1016 := by
  have g0 := part_016_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_016_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_016_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_016_3
  exact g3
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52998007421 : ℝ) / 65536) ((53033567098 : ℝ) / 65536) 1016 := by
  apply RH1E6S14.group_016 <;> assumption

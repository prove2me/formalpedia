-- Prove2me | solution 1 for RH1E6S13.group_030
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T22:20:03.440625+00:00
-- url     : https://prove2.me/submissions/bf911302-689e-4492-9218-ebf577fc24c9

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_030_0
import Theorems.Thm_RH1E6S13_part_030_1
import Theorems.Thm_RH1E6S13_part_030_2
import Theorems.Thm_RH1E6S13_part_030_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_030 : RS5.BandZeros ((50224660202 : ℝ) / 65536) ((50260390214 : ℝ) / 65536) 1016 := by
  have g0 := part_030_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_030_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_030_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_030_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50224660202 : ℝ) / 65536) ((50260390214 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_030 <;> assumption

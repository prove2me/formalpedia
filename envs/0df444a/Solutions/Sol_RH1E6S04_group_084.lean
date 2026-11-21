-- Prove2me | solution 1 for RH1E6S04.group_084
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:13:10.811759+00:00
-- url     : https://prove2.me/submissions/c34b4626-e06e-46dd-a829-5890d6e1bfcd

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_084_0
import Theorems.Thm_RH1E6S04_part_084_1
import Theorems.Thm_RH1E6S04_part_084_2
import Theorems.Thm_RH1E6S04_part_084_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_084 : RS5.BandZeros ((22899191697 : ℝ) / 65536) ((22937497748 : ℝ) / 65536) 1016 := by
  have g0 := part_084_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_084_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_084_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_084_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((22899191697 : ℝ) / 65536) ((22937497748 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_084 <;> assumption

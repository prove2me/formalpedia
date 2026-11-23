-- Prove2me | solution 1 for RH1E6S15.group_014
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:51:50.939449+00:00
-- url     : https://prove2.me/submissions/abe43aa2-87a4-47b7-9557-c5e4c61e5d2d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_014_0
import Theorems.Thm_RH1E6S15_part_014_1
import Theorems.Thm_RH1E6S15_part_014_2
import Theorems.Thm_RH1E6S15_part_014_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_014 : RS5.BandZeros ((56201123644 : ℝ) / 65536) ((56236473506 : ℝ) / 65536) 1016 := by
  have g0 := part_014_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_014_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_014_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_014_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56201123644 : ℝ) / 65536) ((56236473506 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_014 <;> assumption

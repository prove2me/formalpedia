-- Prove2me | solution 1 for RH1E6S15.group_084
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T13:27:00.912667+00:00
-- url     : https://prove2.me/submissions/582ada0a-5c3e-40fc-a5f4-d0bbf4b993f8

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_084_0
import Theorems.Thm_RH1E6S15_part_084_1
import Theorems.Thm_RH1E6S15_part_084_2
import Theorems.Thm_RH1E6S15_part_084_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_084 : RS5.BandZeros ((58673356989 : ℝ) / 65536) ((58708629782 : ℝ) / 65536) 1016 := by
  have g0 := part_084_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_084_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_084_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_084_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((58673356989 : ℝ) / 65536) ((58708629782 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_084 <;> assumption

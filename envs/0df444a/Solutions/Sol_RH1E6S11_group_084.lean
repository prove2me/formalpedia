-- Prove2me | solution 1 for RH1E6S11.group_084
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:25:15.243721+00:00
-- url     : https://prove2.me/submissions/04e09c2c-1cbb-4e0c-8c3a-57c73e26caf2

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_084_0
import Theorems.Thm_RH1E6S11_part_084_1
import Theorems.Thm_RH1E6S11_part_084_2
import Theorems.Thm_RH1E6S11_part_084_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_084 : RS5.BandZeros ((45632723917 : ℝ) / 65536) ((45668731008 : ℝ) / 65536) 1016 := by
  have g0 := part_084_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_084_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_084_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_084_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45632723917 : ℝ) / 65536) ((45668731008 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_084 <;> assumption

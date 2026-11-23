-- Prove2me | solution 1 for RH1E6S15.group_013
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T08:57:36.414162+00:00
-- url     : https://prove2.me/submissions/62337adc-f588-44c1-b2b6-21d4e2cc8540

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_013_0
import Theorems.Thm_RH1E6S15_part_013_1
import Theorems.Thm_RH1E6S15_part_013_2
import Theorems.Thm_RH1E6S15_part_013_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_013 : RS5.BandZeros ((56165703370 : ℝ) / 65536) ((56201123644 : ℝ) / 65536) 1016 := by
  have g0 := part_013_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_013_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_013_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_013_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((56165703370 : ℝ) / 65536) ((56201123644 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_013 <;> assumption

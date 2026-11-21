-- Prove2me | solution 1 for RH1E6S05.group_060
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T15:41:14.823089+00:00
-- url     : https://prove2.me/submissions/3c7ec11f-b3d1-4faa-a6ad-23ea7b04ec77

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_060_0
import Theorems.Thm_RH1E6S05_part_060_1
import Theorems.Thm_RH1E6S05_part_060_2
import Theorems.Thm_RH1E6S05_part_060_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_060 : RS5.BandZeros ((25224545491 : ℝ) / 65536) ((25262506415 : ℝ) / 65536) 1016 := by
  have g0 := part_060_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_060_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_060_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_060_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25224545491 : ℝ) / 65536) ((25262506415 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_060 <;> assumption

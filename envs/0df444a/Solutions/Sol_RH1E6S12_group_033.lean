-- Prove2me | solution 1 for RH1E6S12.group_033
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T09:12:04.892059+00:00
-- url     : https://prove2.me/submissions/15a372c5-e21c-4b05-9178-a5a708a7168d

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_033_0
import Theorems.Thm_RH1E6S12_part_033_1
import Theorems.Thm_RH1E6S12_part_033_2
import Theorems.Thm_RH1E6S12_part_033_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_033 : RS5.BandZeros ((47061941277 : ℝ) / 65536) ((47097839388 : ℝ) / 65536) 1016 := by
  have g0 := part_033_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_033_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_033_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_033_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((47061941277 : ℝ) / 65536) ((47097839388 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_033 <;> assumption

-- Prove2me | solution 1 for RH1E6S01.group_032
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T00:33:47.467697+00:00
-- url     : https://prove2.me/submissions/606e4026-7fb2-4c58-a48a-4cfb1aed97e8

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_032_0
import Theorems.Thm_RH1E6S01_part_032_1
import Theorems.Thm_RH1E6S01_part_032_2
import Theorems.Thm_RH1E6S01_part_032_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_032 : RS5.BandZeros ((11150054818 : ℝ) / 65536) ((11191027334 : ℝ) / 65536) 1016 := by
  have g0 := part_032_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_032_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_032_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_032_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11150054818 : ℝ) / 65536) ((11191027334 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_032 <;> assumption

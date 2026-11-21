-- Prove2me | solution 1 for RH1E6S05.group_070
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T16:12:55.383415+00:00
-- url     : https://prove2.me/submissions/b157ed29-a383-4250-92f0-c57d13bb05b3

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_070_0
import Theorems.Thm_RH1E6S05_part_070_1
import Theorems.Thm_RH1E6S05_part_070_2
import Theorems.Thm_RH1E6S05_part_070_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_070 : RS5.BandZeros ((25603839161 : ℝ) / 65536) ((25641739475 : ℝ) / 65536) 1016 := by
  have g0 := part_070_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_070_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_070_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_070_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((25603839161 : ℝ) / 65536) ((25641739475 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_070 <;> assumption

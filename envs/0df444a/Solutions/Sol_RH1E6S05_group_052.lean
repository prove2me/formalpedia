-- Prove2me | solution 1 for RH1E6S05.group_052
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:39:32.134311+00:00
-- url     : https://prove2.me/submissions/d3265bef-29d7-4613-8875-66a5fc7ce56b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_052_0
import Theorems.Thm_RH1E6S05_part_052_1
import Theorems.Thm_RH1E6S05_part_052_2
import Theorems.Thm_RH1E6S05_part_052_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_052 : RS5.BandZeros ((24920754802 : ℝ) / 65536) ((24958748114 : ℝ) / 65536) 1016 := by
  have g0 := part_052_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_052_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_052_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_052_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24920754802 : ℝ) / 65536) ((24958748114 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_052 <;> assumption

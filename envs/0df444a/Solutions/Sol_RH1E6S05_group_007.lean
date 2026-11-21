-- Prove2me | solution 1 for RH1E6S05.group_007
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:30:45.352673+00:00
-- url     : https://prove2.me/submissions/727cf156-57fe-4cf0-a641-4a2bdca2abe4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_007_0
import Theorems.Thm_RH1E6S05_part_007_1
import Theorems.Thm_RH1E6S05_part_007_2
import Theorems.Thm_RH1E6S05_part_007_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_007 : RS5.BandZeros ((23205458084 : ℝ) / 65536) ((23243689430 : ℝ) / 65536) 1016 := by
  have g0 := part_007_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_007_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_007_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_007_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23205458084 : ℝ) / 65536) ((23243689430 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_007 <;> assumption

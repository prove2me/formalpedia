-- Prove2me | solution 1 for RH1E6S09.group_008
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:42:02.685433+00:00
-- url     : https://prove2.me/submissions/1ce12201-2bea-40f3-9020-aa3540cba507

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_008_0
import Theorems.Thm_RH1E6S09_part_008_1
import Theorems.Thm_RH1E6S09_part_008_2
import Theorems.Thm_RH1E6S09_part_008_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_008 : RS5.BandZeros ((36338776244 : ℝ) / 65536) ((36375521899 : ℝ) / 65536) 1016 := by
  have g0 := part_008_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_008_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_008_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_008_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((36338776244 : ℝ) / 65536) ((36375521899 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_008 <;> assumption

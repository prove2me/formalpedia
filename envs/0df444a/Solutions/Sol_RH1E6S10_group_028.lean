-- Prove2me | solution 1 for RH1E6S10.group_028
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T22:45:38.868969+00:00
-- url     : https://prove2.me/submissions/2d71bc36-095a-4cac-8a40-da1ec0dd90fe

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_028_0
import Theorems.Thm_RH1E6S10_part_028_1
import Theorems.Thm_RH1E6S10_part_028_2
import Theorems.Thm_RH1E6S10_part_028_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_028 : RS5.BandZeros ((40342057643 : ℝ) / 65536) ((40378450636 : ℝ) / 65536) 1016 := by
  have g0 := part_028_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_028_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_028_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_028_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((40342057643 : ℝ) / 65536) ((40378450636 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_028 <;> assumption

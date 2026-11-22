-- Prove2me | solution 1 for RH1E6S10.group_086
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:03:41.229504+00:00
-- url     : https://prove2.me/submissions/4793008a-93e5-4941-95f5-f65bae2a184e

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_086_0
import Theorems.Thm_RH1E6S10_part_086_1
import Theorems.Thm_RH1E6S10_part_086_2
import Theorems.Thm_RH1E6S10_part_086_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_086 : RS5.BandZeros ((42448739603 : ℝ) / 65536) ((42484981114 : ℝ) / 65536) 1016 := by
  have g0 := part_086_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_086_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_086_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_086_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42448739603 : ℝ) / 65536) ((42484981114 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_086 <;> assumption

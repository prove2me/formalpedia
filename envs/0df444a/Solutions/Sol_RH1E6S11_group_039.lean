-- Prove2me | solution 1 for RH1E6S11.group_039
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:02:06.001997+00:00
-- url     : https://prove2.me/submissions/411af29d-adf6-419c-9c8f-3da0368f8881

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_039_0
import Theorems.Thm_RH1E6S11_part_039_1
import Theorems.Thm_RH1E6S11_part_039_2
import Theorems.Thm_RH1E6S11_part_039_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_039 : RS5.BandZeros ((44009417565 : ℝ) / 65536) ((44045563904 : ℝ) / 65536) 1016 := by
  have g0 := part_039_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_039_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_039_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_039_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44009417565 : ℝ) / 65536) ((44045563904 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_039 <;> assumption

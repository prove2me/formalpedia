-- Prove2me | solution 1 for RH1E6S10.group_076
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T02:32:39.558444+00:00
-- url     : https://prove2.me/submissions/aad52a2c-a109-42ed-9bfa-cff660d76c9a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_076_0
import Theorems.Thm_RH1E6S10_part_076_1
import Theorems.Thm_RH1E6S10_part_076_2
import Theorems.Thm_RH1E6S10_part_076_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_076 : RS5.BandZeros ((42086185499 : ℝ) / 65536) ((42122462871 : ℝ) / 65536) 1016 := by
  have g0 := part_076_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_076_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_076_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_076_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((42086185499 : ℝ) / 65536) ((42122462871 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_076 <;> assumption

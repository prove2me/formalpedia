-- Prove2me | solution 1 for RH1E6S10.group_007
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T17:48:13.66759+00:00
-- url     : https://prove2.me/submissions/e6640b8e-2cfb-42da-be0c-11b342c8e86b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_007_0
import Theorems.Thm_RH1E6S10_part_007_1
import Theorems.Thm_RH1E6S10_part_007_2
import Theorems.Thm_RH1E6S10_part_007_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_007 : RS5.BandZeros ((39576942366 : ℝ) / 65536) ((39613396064 : ℝ) / 65536) 1016 := by
  have g0 := part_007_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_007_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_007_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_007_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39576942366 : ℝ) / 65536) ((39613396064 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_007 <;> assumption

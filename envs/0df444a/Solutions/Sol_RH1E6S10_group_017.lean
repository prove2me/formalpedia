-- Prove2me | solution 1 for RH1E6S10.group_017
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:55:38.748117+00:00
-- url     : https://prove2.me/submissions/5e40b614-9dc7-499c-be89-0ff8e542b0b6

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_017_0
import Theorems.Thm_RH1E6S10_part_017_1
import Theorems.Thm_RH1E6S10_part_017_2
import Theorems.Thm_RH1E6S10_part_017_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_017 : RS5.BandZeros ((39941428886 : ℝ) / 65536) ((39977871424 : ℝ) / 65536) 1016 := by
  have g0 := part_017_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_017_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_017_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_017_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39941428886 : ℝ) / 65536) ((39977871424 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_017 <;> assumption

-- Prove2me | solution 1 for RH1E6S10.group_012
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T18:20:30.617993+00:00
-- url     : https://prove2.me/submissions/f3c5bfbb-aaa6-454b-b12a-19d09da9c70f

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S10_part_012_0
import Theorems.Thm_RH1E6S10_part_012_1
import Theorems.Thm_RH1E6S10_part_012_2
import Theorems.Thm_RH1E6S10_part_012_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S10

theorem group_012 : RS5.BandZeros ((39759226500 : ℝ) / 65536) ((39795665611 : ℝ) / 65536) 1016 := by
  have g0 := part_012_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_012_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_012_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_012_3
  exact g3
end RH1E6S10
open RH1E6S10 in
theorem solution : RS5.BandZeros ((39759226500 : ℝ) / 65536) ((39795665611 : ℝ) / 65536) 1016 := by
  apply RH1E6S10.group_012 <;> assumption

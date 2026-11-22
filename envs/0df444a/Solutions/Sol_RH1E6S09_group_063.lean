-- Prove2me | solution 1 for RH1E6S09.group_063
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T13:46:48.855943+00:00
-- url     : https://prove2.me/submissions/3f8590d9-5f18-4872-a80e-a3432bcb7973

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_063_0
import Theorems.Thm_RH1E6S09_part_063_1
import Theorems.Thm_RH1E6S09_part_063_2
import Theorems.Thm_RH1E6S09_part_063_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_063 : RS5.BandZeros ((38354502843 : ℝ) / 65536) ((38391092431 : ℝ) / 65536) 1016 := by
  have g0 := part_063_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_063_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_063_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_063_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((38354502843 : ℝ) / 65536) ((38391092431 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_063 <;> assumption

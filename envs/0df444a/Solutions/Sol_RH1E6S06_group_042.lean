-- Prove2me | solution 1 for RH1E6S06.group_042
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T19:13:06.52361+00:00
-- url     : https://prove2.me/submissions/3d096466-6d23-4267-a8a4-9f77faacb969

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_042_0
import Theorems.Thm_RH1E6S06_part_042_1
import Theorems.Thm_RH1E6S06_part_042_2
import Theorems.Thm_RH1E6S06_part_042_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_042 : RS5.BandZeros ((27798697117 : ℝ) / 65536) ((27836324944 : ℝ) / 65536) 1016 := by
  have g0 := part_042_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_042_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_042_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_042_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((27798697117 : ℝ) / 65536) ((27836324944 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_042 <;> assumption

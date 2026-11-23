-- Prove2me | solution 1 for RH1E6S14.group_043
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:14:06.918737+00:00
-- url     : https://prove2.me/submissions/b52048fa-47d2-476a-925b-10e88ad09912

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_043_0
import Theorems.Thm_RH1E6S14_part_043_1
import Theorems.Thm_RH1E6S14_part_043_2
import Theorems.Thm_RH1E6S14_part_043_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_043 : RS5.BandZeros ((53957366863 : ℝ) / 65536) ((53992888320 : ℝ) / 65536) 1016 := by
  have g0 := part_043_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_043_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_043_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_043_3
  exact g3
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53957366863 : ℝ) / 65536) ((53992888320 : ℝ) / 65536) 1016 := by
  apply RH1E6S14.group_043 <;> assumption

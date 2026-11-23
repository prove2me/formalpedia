-- Prove2me | solution 1 for RH1E6S14.group_003
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:48:25.6218+00:00
-- url     : https://prove2.me/submissions/20936861-7a08-410f-bb50-409a5fd188a0

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_003_0
import Theorems.Thm_RH1E6S14_part_003_1
import Theorems.Thm_RH1E6S14_part_003_2
import Theorems.Thm_RH1E6S14_part_003_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_003 : RS5.BandZeros ((52535568057 : ℝ) / 65536) ((52571141307 : ℝ) / 65536) 1016 := by
  have g0 := part_003_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_003_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_003_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_003_3
  exact g3
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((52535568057 : ℝ) / 65536) ((52571141307 : ℝ) / 65536) 1016 := by
  apply RH1E6S14.group_003 <;> assumption

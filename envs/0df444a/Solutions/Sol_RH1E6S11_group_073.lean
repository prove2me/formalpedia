-- Prove2me | solution 1 for RH1E6S11.group_073
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:41:19.749981+00:00
-- url     : https://prove2.me/submissions/14b932f0-d5b2-4872-83b4-2396d7bd207a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_073_0
import Theorems.Thm_RH1E6S11_part_073_1
import Theorems.Thm_RH1E6S11_part_073_2
import Theorems.Thm_RH1E6S11_part_073_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_073 : RS5.BandZeros ((45236395246 : ℝ) / 65536) ((45272429385 : ℝ) / 65536) 1016 := by
  have g0 := part_073_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_073_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_073_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_073_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45236395246 : ℝ) / 65536) ((45272429385 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_073 <;> assumption

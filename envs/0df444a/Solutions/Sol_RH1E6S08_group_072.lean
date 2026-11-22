-- Prove2me | solution 1 for RH1E6S08.group_072
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T07:33:15.364627+00:00
-- url     : https://prove2.me/submissions/9fcfb84e-9438-4ed4-9d34-a31eb5834def

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_072_0
import Theorems.Thm_RH1E6S08_part_072_1
import Theorems.Thm_RH1E6S08_part_072_2
import Theorems.Thm_RH1E6S08_part_072_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_072 : RS5.BandZeros ((35428039680 : ℝ) / 65536) ((35464864080 : ℝ) / 65536) 1016 := by
  have g0 := part_072_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_072_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_072_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_072_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35428039680 : ℝ) / 65536) ((35464864080 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_072 <;> assumption

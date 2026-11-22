-- Prove2me | solution 1 for RH1E6S08.group_083
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:06:20.723291+00:00
-- url     : https://prove2.me/submissions/4ef1b785-ac61-464b-becf-1fe43b143c9f

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_083_0
import Theorems.Thm_RH1E6S08_part_083_1
import Theorems.Thm_RH1E6S08_part_083_2
import Theorems.Thm_RH1E6S08_part_083_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_083 : RS5.BandZeros ((35832865037 : ℝ) / 65536) ((35869628013 : ℝ) / 65536) 1016 := by
  have g0 := part_083_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_083_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_083_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_083_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35832865037 : ℝ) / 65536) ((35869628013 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_083 <;> assumption

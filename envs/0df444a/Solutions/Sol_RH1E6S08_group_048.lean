-- Prove2me | solution 1 for RH1E6S08.group_048
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T06:27:19.764997+00:00
-- url     : https://prove2.me/submissions/8f144a2e-1ad2-441d-9edb-9c2b3dc45245

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_048_0
import Theorems.Thm_RH1E6S08_part_048_1
import Theorems.Thm_RH1E6S08_part_048_2
import Theorems.Thm_RH1E6S08_part_048_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_048 : RS5.BandZeros ((34543409001 : ℝ) / 65536) ((34580295530 : ℝ) / 65536) 1016 := by
  have g0 := part_048_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_048_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_048_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_048_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((34543409001 : ℝ) / 65536) ((34580295530 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_048 <;> assumption

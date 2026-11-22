-- Prove2me | solution 1 for RH1E6S08.group_084
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T08:08:59.936839+00:00
-- url     : https://prove2.me/submissions/02a36d3a-ad2c-41a5-ae7c-9060b1850c54

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_084_0
import Theorems.Thm_RH1E6S08_part_084_1
import Theorems.Thm_RH1E6S08_part_084_2
import Theorems.Thm_RH1E6S08_part_084_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_084 : RS5.BandZeros ((35869628013 : ℝ) / 65536) ((35906410538 : ℝ) / 65536) 1016 := by
  have g0 := part_084_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_084_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_084_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_084_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((35869628013 : ℝ) / 65536) ((35906410538 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_084 <;> assumption

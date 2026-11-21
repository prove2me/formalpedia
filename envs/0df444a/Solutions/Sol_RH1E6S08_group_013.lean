-- Prove2me | solution 1 for RH1E6S08.group_013
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T04:42:52.558182+00:00
-- url     : https://prove2.me/submissions/2de7576f-12c0-4932-b468-82454d3f739e

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_013_0
import Theorems.Thm_RH1E6S08_part_013_1
import Theorems.Thm_RH1E6S08_part_013_2
import Theorems.Thm_RH1E6S08_part_013_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_013 : RS5.BandZeros ((33249661860 : ℝ) / 65536) ((33286703339 : ℝ) / 65536) 1016 := by
  have g0 := part_013_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_013_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_013_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_013_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33249661860 : ℝ) / 65536) ((33286703339 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_013 <;> assumption

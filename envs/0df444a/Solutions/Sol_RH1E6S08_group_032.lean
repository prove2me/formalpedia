-- Prove2me | solution 1 for RH1E6S08.group_032
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T05:40:37.250721+00:00
-- url     : https://prove2.me/submissions/5808102c-d284-4859-95dc-9ef5d0b33e4e

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S08_part_032_0
import Theorems.Thm_RH1E6S08_part_032_1
import Theorems.Thm_RH1E6S08_part_032_2
import Theorems.Thm_RH1E6S08_part_032_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S08

theorem group_032 : RS5.BandZeros ((33952525233 : ℝ) / 65536) ((33989483830 : ℝ) / 65536) 1016 := by
  have g0 := part_032_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_032_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_032_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_032_3
  exact g3
end RH1E6S08
open RH1E6S08 in
theorem solution : RS5.BandZeros ((33952525233 : ℝ) / 65536) ((33989483830 : ℝ) / 65536) 1016 := by
  apply RH1E6S08.group_032 <;> assumption

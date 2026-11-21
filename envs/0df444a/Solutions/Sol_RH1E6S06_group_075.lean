-- Prove2me | solution 1 for RH1E6S06.group_075
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T22:25:27.242757+00:00
-- url     : https://prove2.me/submissions/c1542420-2dc8-4238-bc49-38091eb36022

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S06_part_075_0
import Theorems.Thm_RH1E6S06_part_075_1
import Theorems.Thm_RH1E6S06_part_075_2
import Theorems.Thm_RH1E6S06_part_075_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S06

theorem group_075 : RS5.BandZeros ((29037779507 : ℝ) / 65536) ((29075243590 : ℝ) / 65536) 1016 := by
  have g0 := part_075_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_075_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_075_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_075_3
  exact g3
end RH1E6S06
open RH1E6S06 in
theorem solution : RS5.BandZeros ((29037779507 : ℝ) / 65536) ((29075243590 : ℝ) / 65536) 1016 := by
  apply RH1E6S06.group_075 <;> assumption

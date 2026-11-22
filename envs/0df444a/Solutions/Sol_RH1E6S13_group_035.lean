-- Prove2me | solution 1 for RH1E6S13.group_035
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T22:50:28.99581+00:00
-- url     : https://prove2.me/submissions/d335d840-f4ba-4b45-a72a-d90eda86de73

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_035_0
import Theorems.Thm_RH1E6S13_part_035_1
import Theorems.Thm_RH1E6S13_part_035_2
import Theorems.Thm_RH1E6S13_part_035_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_035 : RS5.BandZeros ((50403244660 : ℝ) / 65536) ((50438946278 : ℝ) / 65536) 1016 := by
  have g0 := part_035_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_035_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_035_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_035_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50403244660 : ℝ) / 65536) ((50438946278 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_035 <;> assumption

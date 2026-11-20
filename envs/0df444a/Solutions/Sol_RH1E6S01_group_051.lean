-- Prove2me | solution 1 for RH1E6S01.group_051
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T01:14:04.31182+00:00
-- url     : https://prove2.me/submissions/98516837-61f4-4393-bd9b-34e5adfbe3b4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S01_part_051_0
import Theorems.Thm_RH1E6S01_part_051_1
import Theorems.Thm_RH1E6S01_part_051_2
import Theorems.Thm_RH1E6S01_part_051_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S01

theorem group_051 : RS5.BandZeros ((11926266376 : ℝ) / 65536) ((11966981082 : ℝ) / 65536) 1016 := by
  have g0 := part_051_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_051_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_051_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_051_3
  exact g3
end RH1E6S01
open RH1E6S01 in
theorem solution : RS5.BandZeros ((11926266376 : ℝ) / 65536) ((11966981082 : ℝ) / 65536) 1016 := by
  apply RH1E6S01.group_051 <;> assumption

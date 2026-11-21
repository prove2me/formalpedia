-- Prove2me | solution 1 for RH1E6S04.group_051
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:27:44.994063+00:00
-- url     : https://prove2.me/submissions/8e20f52c-6609-413b-9ac4-8d36ff18940b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_051_0
import Theorems.Thm_RH1E6S04_part_051_1
import Theorems.Thm_RH1E6S04_part_051_2
import Theorems.Thm_RH1E6S04_part_051_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_051 : RS5.BandZeros ((21632368050 : ℝ) / 65536) ((21670836586 : ℝ) / 65536) 1016 := by
  have g0 := part_051_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_051_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_051_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_051_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21632368050 : ℝ) / 65536) ((21670836586 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_051 <;> assumption

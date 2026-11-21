-- Prove2me | solution 1 for RH1E6S04.group_018
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T09:13:03.69719+00:00
-- url     : https://prove2.me/submissions/cbc31721-f183-4c7c-b916-e5cd2776db27

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_018_0
import Theorems.Thm_RH1E6S04_part_018_1
import Theorems.Thm_RH1E6S04_part_018_2
import Theorems.Thm_RH1E6S04_part_018_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_018 : RS5.BandZeros ((20358648262 : ℝ) / 65536) ((20397361113 : ℝ) / 65536) 1016 := by
  have g0 := part_018_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_018_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_018_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_018_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((20358648262 : ℝ) / 65536) ((20397361113 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_018 <;> assumption

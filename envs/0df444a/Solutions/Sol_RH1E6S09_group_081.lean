-- Prove2me | solution 1 for RH1E6S09.group_081
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T16:06:07.237928+00:00
-- url     : https://prove2.me/submissions/26c748a2-232f-48f9-b0a4-e1330898f84b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S09_part_081_0
import Theorems.Thm_RH1E6S09_part_081_1
import Theorems.Thm_RH1E6S09_part_081_2
import Theorems.Thm_RH1E6S09_part_081_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S09

theorem group_081 : RS5.BandZeros ((39012179174 : ℝ) / 65536) ((39048696150 : ℝ) / 65536) 1016 := by
  have g0 := part_081_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_081_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_081_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_081_3
  exact g3
end RH1E6S09
open RH1E6S09 in
theorem solution : RS5.BandZeros ((39012179174 : ℝ) / 65536) ((39048696150 : ℝ) / 65536) 1016 := by
  apply RH1E6S09.group_081 <;> assumption

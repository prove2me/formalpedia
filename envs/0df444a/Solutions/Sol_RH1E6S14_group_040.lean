-- Prove2me | solution 1 for RH1E6S14.group_040
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T05:23:07.934025+00:00
-- url     : https://prove2.me/submissions/1adf55f3-d1b4-4ec1-8072-622f948cbaa4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_040_0
import Theorems.Thm_RH1E6S14_part_040_1
import Theorems.Thm_RH1E6S14_part_040_2
import Theorems.Thm_RH1E6S14_part_040_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_040 : RS5.BandZeros ((53850843006 : ℝ) / 65536) ((53886344718 : ℝ) / 65536) 1016 := by
  have g0 := part_040_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_040_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_040_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_040_3
  exact g3
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53850843006 : ℝ) / 65536) ((53886344718 : ℝ) / 65536) 1016 := by
  apply RH1E6S14.group_040 <;> assumption

-- Prove2me | solution 1 for RH1E6S13.group_034
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T22:44:51.596343+00:00
-- url     : https://prove2.me/submissions/2902d786-b67d-4bfc-8505-fc1df89d8f58

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_034_0
import Theorems.Thm_RH1E6S13_part_034_1
import Theorems.Thm_RH1E6S13_part_034_2
import Theorems.Thm_RH1E6S13_part_034_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_034 : RS5.BandZeros ((50367540884 : ℝ) / 65536) ((50403244660 : ℝ) / 65536) 1016 := by
  have g0 := part_034_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_034_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_034_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_034_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((50367540884 : ℝ) / 65536) ((50403244660 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_034 <;> assumption

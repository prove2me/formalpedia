-- Prove2me | solution 1 for RH1E6S03.group_040
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:52:26.654661+00:00
-- url     : https://prove2.me/submissions/2d0cc151-368e-46bf-8671-f1b3c98d77e4

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_040_0
import Theorems.Thm_RH1E6S03_part_040_1
import Theorems.Thm_RH1E6S03_part_040_2
import Theorems.Thm_RH1E6S03_part_040_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_040 : RS5.BandZeros ((17957102416 : ℝ) / 65536) ((17996259937 : ℝ) / 65536) 1016 := by
  have g0 := part_040_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_040_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_040_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_040_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17957102416 : ℝ) / 65536) ((17996259937 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_040 <;> assumption

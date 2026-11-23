-- Prove2me | solution 1 for RH1E6S13.group_063
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T00:53:34.180162+00:00
-- url     : https://prove2.me/submissions/f17e92c7-e97c-4397-9e5d-95fe033c1844

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_063_0
import Theorems.Thm_RH1E6S13_part_063_1
import Theorems.Thm_RH1E6S13_part_063_2
import Theorems.Thm_RH1E6S13_part_063_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_063 : RS5.BandZeros ((51402335300 : ℝ) / 65536) ((51437977226 : ℝ) / 65536) 1016 := by
  have g0 := part_063_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_063_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_063_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_063_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((51402335300 : ℝ) / 65536) ((51437977226 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_063 <;> assumption

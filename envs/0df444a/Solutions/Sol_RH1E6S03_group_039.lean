-- Prove2me | solution 1 for RH1E6S03.group_039
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T06:49:58.638063+00:00
-- url     : https://prove2.me/submissions/3769726c-7075-4b85-9810-75609e10a8fe

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_039_0
import Theorems.Thm_RH1E6S03_part_039_1
import Theorems.Thm_RH1E6S03_part_039_2
import Theorems.Thm_RH1E6S03_part_039_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_039 : RS5.BandZeros ((17917936900 : ℝ) / 65536) ((17957102416 : ℝ) / 65536) 1016 := by
  have g0 := part_039_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_039_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_039_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_039_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((17917936900 : ℝ) / 65536) ((17957102416 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_039 <;> assumption

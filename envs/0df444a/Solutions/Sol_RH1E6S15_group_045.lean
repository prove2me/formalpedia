-- Prove2me | solution 1 for RH1E6S15.group_045
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T10:47:19.664716+00:00
-- url     : https://prove2.me/submissions/9707384b-5021-491d-8fe5-26a25072b224

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_045_0
import Theorems.Thm_RH1E6S15_part_045_1
import Theorems.Thm_RH1E6S15_part_045_2
import Theorems.Thm_RH1E6S15_part_045_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_045 : RS5.BandZeros ((57297078737 : ℝ) / 65536) ((57332392154 : ℝ) / 65536) 1016 := by
  have g0 := part_045_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_045_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_045_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_045_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57297078737 : ℝ) / 65536) ((57332392154 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_045 <;> assumption

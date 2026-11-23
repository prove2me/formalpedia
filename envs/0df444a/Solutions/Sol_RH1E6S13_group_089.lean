-- Prove2me | solution 1 for RH1E6S13.group_089
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T02:28:13.433277+00:00
-- url     : https://prove2.me/submissions/ddaf3a86-deff-48b8-a9f4-5b8dd426778b

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S13_part_089_0
import Theorems.Thm_RH1E6S13_part_089_1
import Theorems.Thm_RH1E6S13_part_089_2
import Theorems.Thm_RH1E6S13_part_089_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S13

theorem group_089 : RS5.BandZeros ((52328573919 : ℝ) / 65536) ((52364170465 : ℝ) / 65536) 1016 := by
  have g0 := part_089_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_089_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_089_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_089_3
  exact g3
end RH1E6S13
open RH1E6S13 in
theorem solution : RS5.BandZeros ((52328573919 : ℝ) / 65536) ((52364170465 : ℝ) / 65536) 1016 := by
  apply RH1E6S13.group_089 <;> assumption

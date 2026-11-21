-- Prove2me | solution 1 for RH1E6S05.group_045
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T14:21:52.938463+00:00
-- url     : https://prove2.me/submissions/177dd6b6-3bcf-4067-8d4e-52b537e3cf33

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_045_0
import Theorems.Thm_RH1E6S05_part_045_1
import Theorems.Thm_RH1E6S05_part_045_2
import Theorems.Thm_RH1E6S05_part_045_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_045 : RS5.BandZeros ((24654644368 : ℝ) / 65536) ((24692674727 : ℝ) / 65536) 1016 := by
  have g0 := part_045_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_045_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_045_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_045_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24654644368 : ℝ) / 65536) ((24692674727 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_045 <;> assumption

-- Prove2me | solution 1 for RH1E6S05.group_010
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T12:38:16.598841+00:00
-- url     : https://prove2.me/submissions/7542f79c-ddab-4ede-b9e4-0608189872c7

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_010_0
import Theorems.Thm_RH1E6S05_part_010_1
import Theorems.Thm_RH1E6S05_part_010_2
import Theorems.Thm_RH1E6S05_part_010_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_010 : RS5.BandZeros ((23320163114 : ℝ) / 65536) ((23358377252 : ℝ) / 65536) 1016 := by
  have g0 := part_010_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_010_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_010_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_010_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((23320163114 : ℝ) / 65536) ((23358377252 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_010 <;> assumption

-- Prove2me | solution 1 for RH1E6S05.group_035
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T13:58:54.169726+00:00
-- url     : https://prove2.me/submissions/5154912e-2d89-4b05-9586-0d8d9e17879a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S05_part_035_0
import Theorems.Thm_RH1E6S05_part_035_1
import Theorems.Thm_RH1E6S05_part_035_2
import Theorems.Thm_RH1E6S05_part_035_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S05

theorem group_035 : RS5.BandZeros ((24274055055 : ℝ) / 65536) ((24312139227 : ℝ) / 65536) 1016 := by
  have g0 := part_035_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_035_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_035_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_035_3
  exact g3
end RH1E6S05
open RH1E6S05 in
theorem solution : RS5.BandZeros ((24274055055 : ℝ) / 65536) ((24312139227 : ℝ) / 65536) 1016 := by
  apply RH1E6S05.group_035 <;> assumption

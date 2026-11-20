-- Prove2me | solution 1 for RH1E6S00.group_054
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T22:43:02.051411+00:00
-- url     : https://prove2.me/submissions/6d56f27d-0100-4315-96a0-19818fce9be8

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_054_0
import Theorems.Thm_RH1E6S00_part_054_1
import Theorems.Thm_RH1E6S00_part_054_2
import Theorems.Thm_RH1E6S00_part_054_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_054 : RS5.BandZeros ((8851198133 : ℝ) / 65536) ((8893106273 : ℝ) / 65536) 1016 := by
  have g0 := part_054_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_054_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_054_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_054_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((8851198133 : ℝ) / 65536) ((8893106273 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_054 <;> assumption

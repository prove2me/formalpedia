-- Prove2me | solution 1 for RH1E6S11.group_087
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:22:20.346435+00:00
-- url     : https://prove2.me/submissions/6ca90bde-5376-4269-a8e0-f14c2ccaab15

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_087_0
import Theorems.Thm_RH1E6S11_part_087_1
import Theorems.Thm_RH1E6S11_part_087_2
import Theorems.Thm_RH1E6S11_part_087_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_087 : RS5.BandZeros ((45740773303 : ℝ) / 65536) ((45776764207 : ℝ) / 65536) 1016 := by
  have g0 := part_087_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_087_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_087_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_087_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((45740773303 : ℝ) / 65536) ((45776764207 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_087 <;> assumption

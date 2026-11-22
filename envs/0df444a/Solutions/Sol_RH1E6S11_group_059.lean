-- Prove2me | solution 1 for RH1E6S11.group_059
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T06:01:39.554796+00:00
-- url     : https://prove2.me/submissions/1cc88e8b-97b8-4a7e-a1f2-31944bbf436f

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_059_0
import Theorems.Thm_RH1E6S11_part_059_1
import Theorems.Thm_RH1E6S11_part_059_2
import Theorems.Thm_RH1E6S11_part_059_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_059 : RS5.BandZeros ((44731532197 : ℝ) / 65536) ((44767592319 : ℝ) / 65536) 1016 := by
  have g0 := part_059_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_059_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_059_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_059_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44731532197 : ℝ) / 65536) ((44767592319 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_059 <;> assumption

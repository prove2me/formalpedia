-- Prove2me | solution 1 for RH1E6S00.group_027
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:49:24.507312+00:00
-- url     : https://prove2.me/submissions/f888d8e1-40f5-401f-8acb-e5ca0bf278ff

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_027_0
import Theorems.Thm_RH1E6S00_part_027_1
import Theorems.Thm_RH1E6S00_part_027_2
import Theorems.Thm_RH1E6S00_part_027_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_027 : RS5.BandZeros ((7711155025 : ℝ) / 65536) ((7753648737 : ℝ) / 65536) 1016 := by
  have g0 := part_027_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_027_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_027_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_027_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7711155025 : ℝ) / 65536) ((7753648737 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_027 <;> assumption

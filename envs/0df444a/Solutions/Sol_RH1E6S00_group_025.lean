-- Prove2me | solution 1 for RH1E6S00.group_025
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-19T21:44:45.736506+00:00
-- url     : https://prove2.me/submissions/c500a890-83d5-4a5c-a8ac-7b7e2a588c1a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S00_part_025_0
import Theorems.Thm_RH1E6S00_part_025_1
import Theorems.Thm_RH1E6S00_part_025_2
import Theorems.Thm_RH1E6S00_part_025_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S00

theorem group_025 : RS5.BandZeros ((7626054074 : ℝ) / 65536) ((7668595616 : ℝ) / 65536) 1016 := by
  have g0 := part_025_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_025_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_025_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_025_3
  exact g3
end RH1E6S00
open RH1E6S00 in
theorem solution : RS5.BandZeros ((7626054074 : ℝ) / 65536) ((7668595616 : ℝ) / 65536) 1016 := by
  apply RH1E6S00.group_025 <;> assumption

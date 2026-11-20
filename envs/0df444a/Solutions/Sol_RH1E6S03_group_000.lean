-- Prove2me | solution 1 for RH1E6S03.group_000
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T05:21:19.753225+00:00
-- url     : https://prove2.me/submissions/81b02907-b7e6-4155-9e7c-330efd3b3354

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S03_part_000_0
import Theorems.Thm_RH1E6S03_part_000_1
import Theorems.Thm_RH1E6S03_part_000_2
import Theorems.Thm_RH1E6S03_part_000_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S03

theorem group_000 : RS5.BandZeros ((16384000000 : ℝ) / 65536) ((16423471394 : ℝ) / 65536) 1016 := by
  have g0 := part_000_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_000_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_000_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_000_3
  exact g3
end RH1E6S03
open RH1E6S03 in
theorem solution : RS5.BandZeros ((16384000000 : ℝ) / 65536) ((16423471394 : ℝ) / 65536) 1016 := by
  apply RH1E6S03.group_000 <;> assumption

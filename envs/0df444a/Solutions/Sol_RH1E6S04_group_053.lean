-- Prove2me | solution 1 for RH1E6S04.group_053
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T10:32:46.087533+00:00
-- url     : https://prove2.me/submissions/771c9da7-8c1c-40e6-a0fa-6e707d44787a

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S04_part_053_0
import Theorems.Thm_RH1E6S04_part_053_1
import Theorems.Thm_RH1E6S04_part_053_2
import Theorems.Thm_RH1E6S04_part_053_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S04

theorem group_053 : RS5.BandZeros ((21709327245 : ℝ) / 65536) ((21747802163 : ℝ) / 65536) 1016 := by
  have g0 := part_053_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_053_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_053_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_053_3
  exact g3
end RH1E6S04
open RH1E6S04 in
theorem solution : RS5.BandZeros ((21709327245 : ℝ) / 65536) ((21747802163 : ℝ) / 65536) 1016 := by
  apply RH1E6S04.group_053 <;> assumption

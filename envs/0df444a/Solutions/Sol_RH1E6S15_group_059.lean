-- Prove2me | solution 1 for RH1E6S15.group_059
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T11:40:11.128801+00:00
-- url     : https://prove2.me/submissions/0fc06111-e305-47a2-8d59-f708708f5cc0

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S15_part_059_0
import Theorems.Thm_RH1E6S15_part_059_1
import Theorems.Thm_RH1E6S15_part_059_2
import Theorems.Thm_RH1E6S15_part_059_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S15

theorem group_059 : RS5.BandZeros ((57791454734 : ℝ) / 65536) ((57826741225 : ℝ) / 65536) 1016 := by
  have g0 := part_059_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_059_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_059_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_059_3
  exact g3
end RH1E6S15
open RH1E6S15 in
theorem solution : RS5.BandZeros ((57791454734 : ℝ) / 65536) ((57826741225 : ℝ) / 65536) 1016 := by
  apply RH1E6S15.group_059 <;> assumption

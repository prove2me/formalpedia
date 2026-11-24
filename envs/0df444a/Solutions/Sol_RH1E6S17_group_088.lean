-- Prove2me | solution 1 for RH1E6S17.group_088
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:40:39.868492+00:00
-- url     : https://prove2.me/submissions/224da90a-4d2a-42ee-8630-6226149e864c

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S17_part_088_0
import Theorems.Thm_RH1E6S17_part_088_1
import Theorems.Thm_RH1E6S17_part_088_2
import Theorems.Thm_RH1E6S17_part_088_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S17

theorem group_088 : RS5.BandZeros ((65339862183 : ℝ) / 65536) ((65374798852 : ℝ) / 65536) 1016 := by
  have g0 := part_088_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_088_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_088_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_088_3
  exact g3
end RH1E6S17
open RH1E6S17 in
theorem solution : RS5.BandZeros ((65339862183 : ℝ) / 65536) ((65374798852 : ℝ) / 65536) 1016 := by
  apply RH1E6S17.group_088 <;> assumption

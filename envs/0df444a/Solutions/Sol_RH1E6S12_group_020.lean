-- Prove2me | solution 1 for RH1E6S12.group_020
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T08:37:15.32238+00:00
-- url     : https://prove2.me/submissions/e76f10a4-3af1-4cc8-a0cc-3cca09968bac

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_020_0
import Theorems.Thm_RH1E6S12_part_020_1
import Theorems.Thm_RH1E6S12_part_020_2
import Theorems.Thm_RH1E6S12_part_020_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_020 : RS5.BandZeros ((46594742541 : ℝ) / 65536) ((46630713421 : ℝ) / 65536) 1016 := by
  have g0 := part_020_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_020_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_020_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_020_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46594742541 : ℝ) / 65536) ((46630713421 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_020 <;> assumption

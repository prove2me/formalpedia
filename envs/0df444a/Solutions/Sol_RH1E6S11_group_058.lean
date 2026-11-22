-- Prove2me | solution 1 for RH1E6S11.group_058
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T05:58:44.189827+00:00
-- url     : https://prove2.me/submissions/6eae99c6-6eda-423e-aaff-0585f8c6fe87

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S11_part_058_0
import Theorems.Thm_RH1E6S11_part_058_1
import Theorems.Thm_RH1E6S11_part_058_2
import Theorems.Thm_RH1E6S11_part_058_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S11

theorem group_058 : RS5.BandZeros ((44695434054 : ℝ) / 65536) ((44731532197 : ℝ) / 65536) 1016 := by
  have g0 := part_058_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_058_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_058_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_058_3
  exact g3
end RH1E6S11
open RH1E6S11 in
theorem solution : RS5.BandZeros ((44695434054 : ℝ) / 65536) ((44731532197 : ℝ) / 65536) 1016 := by
  apply RH1E6S11.group_058 <;> assumption

-- Prove2me | solution 1 for RH1E6S12.group_006
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-22T07:53:50.929091+00:00
-- url     : https://prove2.me/submissions/6eae1233-472b-4120-a233-834d7af13fca

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S12_part_006_0
import Theorems.Thm_RH1E6S12_part_006_1
import Theorems.Thm_RH1E6S12_part_006_2
import Theorems.Thm_RH1E6S12_part_006_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S12

theorem group_006 : RS5.BandZeros ((46091183027 : ℝ) / 65536) ((46127153456 : ℝ) / 65536) 1016 := by
  have g0 := part_006_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_006_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_006_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_006_3
  exact g3
end RH1E6S12
open RH1E6S12 in
theorem solution : RS5.BandZeros ((46091183027 : ℝ) / 65536) ((46127153456 : ℝ) / 65536) 1016 := by
  apply RH1E6S12.group_006 <;> assumption

-- Prove2me | solution 1 for RH1E6S07.group_075
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-21T02:38:39.213742+00:00
-- url     : https://prove2.me/submissions/8799757d-c8a7-4e94-ba6f-139a7b640958

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S07_part_075_0
import Theorems.Thm_RH1E6S07_part_075_1
import Theorems.Thm_RH1E6S07_part_075_2
import Theorems.Thm_RH1E6S07_part_075_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S07

theorem group_075 : RS5.BandZeros ((32286485195 : ℝ) / 65536) ((32323591860 : ℝ) / 65536) 1016 := by
  have g0 := part_075_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_075_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_075_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_075_3
  exact g3
end RH1E6S07
open RH1E6S07 in
theorem solution : RS5.BandZeros ((32286485195 : ℝ) / 65536) ((32323591860 : ℝ) / 65536) 1016 := by
  apply RH1E6S07.group_075 <;> assumption

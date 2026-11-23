-- Prove2me | solution 1 for RH1E6S14.group_030
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-23T04:32:04.48798+00:00
-- url     : https://prove2.me/submissions/70726ab7-4432-408e-a96b-bd5de1c41bfc

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S14_part_030_0
import Theorems.Thm_RH1E6S14_part_030_1
import Theorems.Thm_RH1E6S14_part_030_2
import Theorems.Thm_RH1E6S14_part_030_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S14

theorem group_030 : RS5.BandZeros ((53495634766 : ℝ) / 65536) ((53531155180 : ℝ) / 65536) 1016 := by
  have g0 := part_030_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_030_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_030_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_030_3
  exact g3
end RH1E6S14
open RH1E6S14 in
theorem solution : RS5.BandZeros ((53495634766 : ℝ) / 65536) ((53531155180 : ℝ) / 65536) 1016 := by
  apply RH1E6S14.group_030 <;> assumption

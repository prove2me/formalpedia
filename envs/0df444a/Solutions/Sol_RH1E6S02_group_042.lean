-- Prove2me | solution 1 for RH1E6S02.group_042
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-20T03:46:38.049179+00:00
-- url     : https://prove2.me/submissions/8c3f767d-25a5-4720-93f8-ff56a8710172

import Definitions.Def_ArdaRS_BandSharp
import Theorems.Thm_RH1E6S02_part_042_0
import Theorems.Thm_RH1E6S02_part_042_1
import Theorems.Thm_RH1E6S02_part_042_2
import Theorems.Thm_RH1E6S02_part_042_3
import Theorems.Thm_RS5_BandZeros_glue
import Theorems.Thm_RS5_bandZeros_of_ok_prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH1E6S02

theorem group_042 : RS5.BandZeros ((14791903950 : ℝ) / 65536) ((14831802613 : ℝ) / 65536) 1016 := by
  have g0 := part_042_0
  have g1 := RS5.BandZeros.glue (by norm_num) (by norm_num) g0 part_042_1
  have g2 := RS5.BandZeros.glue (by norm_num) (by norm_num) g1 part_042_2
  have g3 := RS5.BandZeros.glue (by norm_num) (by norm_num) g2 part_042_3
  exact g3
end RH1E6S02
open RH1E6S02 in
theorem solution : RS5.BandZeros ((14791903950 : ℝ) / 65536) ((14831802613 : ℝ) / 65536) 1016 := by
  apply RH1E6S02.group_042 <;> assumption
